-- Prove2me | Theorems.Thm_APSCounting893_Main_implicit_short_integer_sums_in_ch
-- name    : APSCounting893.Main.implicit_short_integer_sums_in_ch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T21:04:38.207638+00:00
-- url     : https://prove2.me/theorems/6a2599ef-10fb-40d1-ab99-7b3de65418f0
-- title:
--   Implicit sums of exponentially many short integers stay in CH
-- statement:
--   Let $F$ be a total natural-valued function on binary words whose output length is bounded by fixed natural numbers $e,f$:
--   $$\operatorname{bits}(F(y))\le e(|y|+1)^f.$$
--   For fixed natural numbers $a,b$, put $r=a(|x|+1)^b$ and define the actual implicit sum
--   $$S(x)=\sum_{i=0}^{2^r-1}F\bigl(\operatorname{frame}(x)\,\Vert\,\operatorname{bits}_r(i)\bigr).$$
--   If the value graph of $F$ belongs to counting level $j$, then the value graph of $S$ belongs to level $j+11$. Moreover,
--   $$\operatorname{bits}(S(x))\le
--   \bigl(a+e(a+4)^f+2\bigr)(|x|+1)^{\max\{b,(b+1)f\}}.$$
--
--   All resource constants and the relative hierarchy overhead precede the input word. This supplies uniform short-integer iterated addition for implicit Chinese remainder arithmetic without constructing the exponentially long list of summands.
-- source:
--   Implicit short-integer form of the iterated-addition steps in Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, author manuscript Section 4, Lemmas 4.1 and 4.3, pp. 9–10, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Used in the arithmetic-to-threshold argument of Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. The explicit eleven-level overhead comes from the published finite-machine comparison, counting and graph interfaces.

import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.implicit_short_integer_sums_in_ch
    (F : Word → ℕ) (j a b e f : ℕ)
    (hF : ∀ x,(F x).bits.length ≤ polyBound e f x.length)
    (hgraph : AtCHLevel j (NaturalGraphLanguage F)) :
    AtCHLevel (j+11) (NaturalGraphLanguage (indexedNaturalSum F a b)) ∧
      ∀ x,(indexedNaturalSum F a b x).bits.length ≤
        polyBound (a+e*(a+4)^f+2) (max b ((b+1)*f)) x.length := by sorry
