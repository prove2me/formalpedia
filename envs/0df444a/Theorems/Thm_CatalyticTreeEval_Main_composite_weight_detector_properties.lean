-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_composite_weight_detector_properties
-- name    : CatalyticTreeEval.Main.composite_weight_detector_properties
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T02:01:12.945193+00:00
-- url     : https://prove2.me/theorems/a04142a4-d003-4d72-8737-e7e194c95f95
-- title:
--   Composite weight detector: degree and Boolean separation
-- statement:
--   Let $p_i$ be distinct primes, $e_i$ nonnegative integers, $m=\prod_i p_i$, and $\Delta=\max_i p_i^{e_i}$. For $w<\prod_i p_i^{e_i}$, the CRT combination of the explicit prime-power detectors is multilinear of degree at most $\Delta-1$. For Boolean $x$ of weight at most $w$, its value is zero at weight $w$; at every smaller weight it is a nonzero canonical residue (each prime projection is zero or one).
--
--   $$\operatorname{wt}(x)=w\Rightarrow f(x)=0,\qquad \operatorname{wt}(x)<w\Rightarrow f(x)\in S\setminus\{0\}.$$
--
--   This establishes the algebraic part of Corollary B.6 for a fixed polynomial construction; its uniform sparse printer is a separate computational obligation.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Corollary B.6.

import Definitions.Def_CatalyticTreeEval_CompositeDetector

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem composite_weight_detector_properties {t : ℕ} (p e : Fin t → ℕ)
    (hp : PrimeData p) (w H : ℕ) (hw : w < ∏ i, p i ^ e i) :
    Multilinear (compositeWeightDetector p e hp w H) ∧
    (compositeWeightDetector p e hp w H).totalDegree ≤ delta p e - 1 ∧
    (∀ x : Fin H → Bool, weight x ≤ w →
      (weight x = w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) = 0) ∧
      (weight x < w → MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ∈
        canonical p (modulus p) ∧
        MvPolynomial.eval (boolPoint x) (compositeWeightDetector p e hp w H) ≠ 0)) := by sorry

end CatalyticTreeEval.Main
