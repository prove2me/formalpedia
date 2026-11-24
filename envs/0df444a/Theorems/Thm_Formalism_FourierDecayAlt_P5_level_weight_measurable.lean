-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_level_weight_measurable
-- name    : Formalism.FourierDecayAlt.P5.level_weight_measurable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:41:53.191925+00:00
-- url     : https://prove2.me/theorems/ac6a0536-ad3a-4cb6-8308-1f77f6649c68
-- title:
--   P5: level weight measurable
-- statement:
--   The P5 construction uses the level weight measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L92-L94

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

theorem Formalism.FourierDecayAlt.P5.level_weight_measurable {β : Type} [MeasurableSpace β] (i : Fin (r + 1)) :
    Measurable (fun q : Cf r i × β => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ)) := by sorry
