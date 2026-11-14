-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_weight_detector_print
-- name    : CatalyticTreeEval.Main.weight_detector_print
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T01:44:45.149393+00:00
-- url     : https://prove2.me/theorems/dbc9e648-b7a0-41f6-9a0c-7fc62c0c6ed2
-- title:
--   Uniform sparse printing of the explicit prime-power weight detector
-- statement:
--   One finite binary machine prints a sparse presentation of the specified prime-power weight detector for every prime, exponent, target weight and positive variable count. Its work prefix is bounded by a uniform constant times p^e log2(H+1) plus log2 p. The printer must output the explicit detector used by the algebraic correctness theorem. This is the computational component of Lemma B.5.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemmas B.4 and B.5.

import Definitions.Def_CatalyticTreeEval_WeightDetector

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- Uniform sparse printing is separate from the verified detector's algebraic properties. -/
theorem weight_detector_print :
    ∃ (M : Machine) (C : ℝ), 0 < C ∧
      ∀ (p e w H : ℕ), Nat.Prime p → 1 ≤ H →
        PolyPrint M (natsCode [p,e,w,H]) (weightDetector p e w H)
          (C * ((p ^ e : ℕ) * log₂ (H + 1) + log₂ p)) := by sorry

end CatalyticTreeEval.Main
