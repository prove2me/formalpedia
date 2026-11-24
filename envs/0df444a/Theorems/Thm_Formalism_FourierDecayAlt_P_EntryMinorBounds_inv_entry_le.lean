-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_inv_entry_le
-- name    : Formalism.FourierDecayAlt.P.EntryMinorBounds.inv_entry_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:33:34.009679+00:00
-- url     : https://prove2.me/theorems/dc203ddd-0046-4021-8f0a-7d45f961adbd
-- title:
--   Entry Minor Bounds: inv entry le
-- statement:
--   The Entry Minor Bounds construction uses the inv entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryMinorBounds.lean#L28-L42

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

theorem Formalism.FourierDecayAlt.P.EntryMinorBounds.inv_entry_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hdet : M.det = 1) (X : ℝ) (hX : 1 ≤ X)
    (hM : ∀ i j, ‖M i j‖ ≤ X) (i j : Fin n) : ‖M⁻¹ i j‖ ≤ (Nat.factorial n : ℝ) * X ^ (n - 1) := by sorry
