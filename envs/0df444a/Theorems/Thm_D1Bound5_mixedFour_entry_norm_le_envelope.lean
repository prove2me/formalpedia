-- Prove2me | Theorems.Thm_D1Bound5_mixedFour_entry_norm_le_envelope
-- name    : D1Bound5.mixedFour_entry_norm_le_envelope
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:33:39.618486+00:00
-- url     : https://prove2.me/theorems/dbad73ad-8b29-4488-aa96-751f8c36a3ea
-- title:
--   Mixed Four entry norm le envelope
-- statement:
--   Any complex matrix obeying the mixed first-row and lower-block entry bounds is entrywise dominated by the exact rational envelope.
-- source:
--   D1Bound5/WeightedRowCertificate.lean, lines 54-72, SHA-256 24e91527c5f644ec2b6289935e81e061377a21fe404f3e2ef431b87e3d5e91b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_WeightedRowCertificate_Definitions

section
namespace D1Bound5















end D1Bound5

namespace D1Bound5


theorem _root_.D1Bound5.mixedFour_entry_norm_le_envelope
    (E : Matrix (Fin 4) (Fin 4) ℂ)
    (hdiag : ∀ i, E i i = 0)
    (hfirst : ∀ i j, i ≠ j → i = 0 ∨ j = 0 →
      ‖E i j‖ < (1 / 18 : ℝ))
    (hlater : ∀ i j, i ≠ j → ¬(i = 0 ∨ j = 0) →
      ‖E i j‖ < (1 / 64 : ℝ))
    (i j : Fin 4) :
    ‖E i j‖ ≤ mixedFourEnvelope i j := by sorry



end D1Bound5
end
