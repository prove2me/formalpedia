-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_mul_entry_le
-- name    : Formalism.FourierDecayAlt.P.NormEntryBounds.mul_entry_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:16.615074+00:00
-- url     : https://prove2.me/theorems/4d1e2e5d-55cc-4670-a713-2ac63e0bf03c
-- title:
--   Norm Entry Bounds: mul entry le
-- statement:
--   The Norm Entry Bounds construction uses the mul entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormEntryBounds.lean#L36-L47

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open Formalism.FourierDecayAlt.P.NormEntryBounds
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.NormEntryBounds.mul_entry_le (A M : B.Mat k r) (a b : ℝ) (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖M i j‖ ≤ b)
    (hb0 : 0 ≤ b) (i j : Fin (2 * r + k + 1)) :
    ‖(A * M) i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (a * b) := by sorry
