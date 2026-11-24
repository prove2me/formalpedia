-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_integral_top_level_point
-- name    : Formalism.FourierDecayAlt.P5.integral_top_level_point
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:40:46.020479+00:00
-- url     : https://prove2.me/theorems/018c0e0f-8050-4e71-beb6-515c9a557aa8
-- title:
--   P5: integral top level point
-- statement:
--   The P5 construction uses the integral top level point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L107-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L107-L115

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {r : ℕ}

theorem Formalism.FourierDecayAlt.P5.integral_top_level_point {β E : Type} [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure β) [SFinite ν]
    (f : Cf r (Fin.last r) × β → E) :
    (Integrable f (volume.prod ν) ↔ Integrable (fun g => f (lastLevelPoint r, g)) ν) ∧
      ∫ q, f q ∂(volume.prod ν) = ∫ g, f (lastLevelPoint r, g) ∂ν := by sorry
