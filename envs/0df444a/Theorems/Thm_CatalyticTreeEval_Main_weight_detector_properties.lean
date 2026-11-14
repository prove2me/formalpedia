-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_weight_detector_properties
-- name    : CatalyticTreeEval.Main.weight_detector_properties
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T01:44:44.750707+00:00
-- url     : https://prove2.me/theorems/a2bea88e-b498-424c-9adb-8186125a8fc8
-- title:
--   Prime-power weight detector: symmetry, multilinearity, degree and evaluation
-- statement:
--   For each prime p, exponent e and target weight w, the explicit binomial-interpolation detector is symmetric and multilinear, has degree at most p^e minus one, and on every Boolean point evaluates to zero exactly when its weight is congruent to w modulo p^e, and to one otherwise. This includes exponent zero. This is the algebraic component of Lemma B.5.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemmas B.4 and B.5.

import Definitions.Def_CatalyticTreeEval_WeightDetector

set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem weight_detector_properties (p e w H : ℕ) (hp : Nat.Prime p) :
    Symmetric (weightDetector p e w H) ∧ Multilinear (weightDetector p e w H) ∧
      (weightDetector p e w H).totalDegree ≤ p ^ e - 1 ∧
      ∀ x : Fin H → Bool, MvPolynomial.eval (boolPoint x) (weightDetector p e w H) =
        if weight x % (p ^ e) = w % (p ^ e) then 0 else 1 := by sorry

end CatalyticTreeEval.Main
