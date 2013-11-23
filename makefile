default: ren-sub.pdf

clean:
	rm RenSub.pdf
	rm RenSub.aux
	rm RenSub.ptb
	rm *.*~

ren-sub.pdf:
	lhs2TeX --agda RenSub.lagda > RenSub.tex
	pdflatex RenSub.tex
show:
	evince RenSub.pdf &

