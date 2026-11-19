-- Prove2me | Theorems.Thm_APSCounting893_Main_implicit_long_integer_sums_in_ch
-- name    : APSCounting893.Main.implicit_long_integer_sums_in_ch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T22:02:59.324258+00:00
-- url     : https://prove2.me/theorems/6f8db617-121e-4266-b0c9-68dbbf1f320a
-- title:
--   Bit access to implicit sums of long integers stays in CH
-- statement:
--   Let $F$ be a total natural-valued function on binary words. Assume that its bit language, with a length-delimited input and a binary bit index, belongs to counting level $j$. For fixed natural numbers $a,b$, set $r=a(|x|+1)^b$ and define the actual sum
--   $$S(x)=\sum_{i=0}^{2^r-1} F\bigl(\operatorname{frame}(x)\,\Vert\,\operatorname{bits}_r(i)\bigr).$$
--   Then
--   $$\operatorname{Bit}(S)\in C_{j+22}P.$$
--   There is no hypothesis on the bit length of $F(x)$. The relative hierarchy overhead and all machine resource constants precede the input word and the queried bit index.
--   This supplies uniform iterated addition for exponentially indexed integer families, including the long dyadic numerators used in Chinese remainder comparison.
-- source:
--   Iterated-addition ingredient in Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, author manuscript Section 3, p. 7, and Section 4, Lemma 4.3, pp. 10–11, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Explicit finite oracle-machine bit-language implementation for Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. The relative level 22 is an implementation bound proved here, not a numerical level claimed by either source.

import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.implicit_long_integer_sums_in_ch (F : Word → ℕ) (j a b : ℕ)
    (hF : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+22) (NaturalBitLanguage (indexedNaturalSum F a b)) := by sorry
