-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_smooth_decay_of_weighted
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_decay_of_weighted
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:18:40.357554+00:00
-- url     : https://prove2.me/theorems/cf1f2859-8747-42aa-b349-2d3a4727445c
-- title:
--   Fou: smooth decay of weighted
-- statement:
--   The Fou construction uses the smooth decay of weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothDecayOfWeighted.lean#L93-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothDecayOfWeighted.lean#L93-L108

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormIteratedFDerivWithinInvOneLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothDecayOfWeighted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
open scoped Nat
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.smooth_decay_of_weighted [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by sorry
