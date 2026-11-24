-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_det_norm_le
-- name    : Formalism.FourierDecayAlt.P.EntryMinorBounds.det_norm_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:33:19.059641+00:00
-- url     : https://prove2.me/theorems/fb1f0cc2-a11d-4f1d-b8d2-cfb3bc1fc7bc
-- title:
--   Entry Minor Bounds: det norm le
-- statement:
--   The Entry Minor Bounds construction uses the det norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L9-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L9-L26

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.EntryMinorBounds

theorem Formalism.FourierDecayAlt.P.EntryMinorBounds.det_norm_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (R : Fin n → ℝ) (hR : ∀ i j, ‖A i j‖ ≤ R i) :
    ‖A.det‖ ≤ (Nat.factorial n : ℝ) * ∏ i, R i := by sorry
