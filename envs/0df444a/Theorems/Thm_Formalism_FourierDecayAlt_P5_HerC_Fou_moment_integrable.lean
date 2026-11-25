-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_moment_integrable
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.moment_integrable
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:23:47.479296+00:00
-- url     : https://prove2.me/theorems/2c7f4095-0cb2-4356-8041-00e8ca245227
-- title:
--   Fou: moment integrable
-- statement:
--   The Fou construction uses the moment integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MomentIntegrable.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MomentIntegrable.lean#L15-L40

import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MomentIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Module
open scoped FourierTransform
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.moment_integrable {u : V → ℂ} (hu : Continuous u) (m : ℕ) (C : ℝ)
    (hdec : ∀ w, ‖u w‖ ≤ C * (1 + ‖w‖) ^ (-((m : ℝ) + finrank ℝ V + 1))) (n : ℕ) (hn : n ≤ m) :
    Integrable (fun v => ‖v‖ ^ n * ‖u v‖) := by sorry
