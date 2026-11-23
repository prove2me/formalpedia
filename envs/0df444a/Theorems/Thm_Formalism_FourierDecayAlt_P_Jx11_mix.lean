-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx11_mix
-- name    : Formalism.FourierDecayAlt.P.Jx11.mix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:32.029605+00:00
-- url     : https://prove2.me/theorems/bb18c2fc-65dd-453f-9264-b641521020e8
-- title:
--   Jx11: mix
-- statement:
--   The Jx11 construction uses the mix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThresholdBelowOne.lean#L32-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThresholdBelowOne.lean#L32-L70

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdBelowOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx11

theorem Formalism.FourierDecayAlt.P.Jx11.mix {L d : ℕ} (grid : Fin L → Fin (d + 1) → ℝ) (S : Fin L → ℝ)
    (hS : ∀ a, ∑ i, |F7.lagCo (grid a) i| = S a) (hpos : ∀ a, 0 < S a) (z : ℂ)
    (Fj : (Fin L → Fin (d + 1)) → ℂ)
    (hz : z = ∑ j : Fin L → Fin (d + 1), ((∏ a, F7.lagCo (grid a) (j a) : ℝ) : ℂ) * Fj j) (c : ℝ)
    (Mj : (Fin L → Fin (d + 1)) → ℝ) (hF : ∀ j, ‖Fj j‖ ≤ c * Mj j) :
    (∀ j, 0 ≤ F7.thGrid grid j) ∧ ∑ j, F7.thGrid grid j = 1 ∧
      ‖z‖ ≤ (∏ a, S a) * (c * ∑ j, F7.thGrid grid j * Mj j) := by sorry
