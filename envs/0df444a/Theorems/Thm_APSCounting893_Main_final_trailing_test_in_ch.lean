-- Prove2me | Theorems.Thm_APSCounting893_Main_final_trailing_test_in_ch
-- name    : APSCounting893.Main.final_trailing_test_in_ch
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:26:26.301988+00:00
-- url     : https://prove2.me/theorems/efc92999-348c-4852-98c5-f88d0f204fce
-- title:
--   Lemma 6.5 — The final trailing-coefficient test in CH
-- statement:
--   Fix $k$ and a family of nonzero rational polynomials $R_x(t_1,\ldots,t_k,T)$ indexed by binary words $x$. Suppose one polynomial in $|x|$ bounds all degrees and numerator and denominator representation bit lengths exponentially, and the individual coefficient-bit language belongs to a fixed level of $\mathrm{CH}$. Then
--
--   $$\{x:(\mathrm{TC}_{t_k}\cdots\mathrm{TC}_{t_1}R_x)(0)=0\}\in\mathrm{CH}.$$
--
--   The resulting level is fixed for the entire family. The source premises concern coefficient representations, degree and height, not a pre-supplied oracle for this vanishing predicate.
--
--   Differences from the source:
--   - encoding: a succinct input-indexed polynomial with fixed k and uniform bounds → a word-indexed family, one coefficient representation, one fixed k and existential uniform polynomial bounds; reason: states the source complexity claim as a uniform family theorem rather than a tautology about one hardcoded polynomial
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Lemma 6.5, p. 26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_CoefficientLanguages

set_option autoImplicit false

namespace APSCounting893.Main

theorem final_trailing_test_in_ch (k : ℕ) (R : Word → MvPolynomial (Fin (k + 1)) ℚ)
    (rho : CoefficientRepresentation k) (hnonzero : ∀ x, R x ≠ 0)
    (hrep : RepresentsPolynomialFamily R rho) (hbound : SinglyExponentialFamily R rho)
    (hbits : InCountingHierarchy (CoefficientBitLanguage rho)) :
    InCountingHierarchy (TrailingZeroLanguage R) := by sorry

end APSCounting893.Main
