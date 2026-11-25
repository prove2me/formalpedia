-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_HerC_Fou_integrable_of_decay
-- name    : Formalism.FourierDecayAlt.P5.HerC.Fou.integrable_of_decay
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:03.774017+00:00
-- url     : https://prove2.me/theorems/02fcae7b-99a4-54ff-92a3-dfebdbc11f7d
-- title:
--   Fou: integrable of decay
-- statement:
--   The Fou construction uses the integrable of decay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralIteratedFDerivEqZero.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralIteratedFDerivEqZero.lean#L24-L27

import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralIteratedFDerivEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerC Formalism.FourierDecayAlt.P5.HerC.Fou
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V]

theorem Formalism.FourierDecayAlt.P5.HerC.Fou.integrable_of_decay {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {u : V → W} (hu : Continuous u)
    (C : ℝ) (hdec : ∀ x, ‖u x‖ ≤ C * (1 + ‖x‖) ^ (-((finrank ℝ V : ℝ) + 1))) : Integrable u := by sorry
