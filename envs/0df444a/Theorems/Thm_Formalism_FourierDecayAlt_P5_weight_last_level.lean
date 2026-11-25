-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_weight_last_level
-- name    : Formalism.FourierDecayAlt.P5.weight_last_level
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:00.075085+00:00
-- url     : https://prove2.me/theorems/e988424f-d1c6-563b-91d6-e555a7f802a8
-- title:
--   P5: weight last level
-- statement:
--   The P5 construction uses the weight last level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L120-L120

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

theorem Formalism.FourierDecayAlt.P5.weight_last_level (a : Cf r (Fin.last r)) : (∏ l, ‖a l‖ ^ (-2 : ℤ)) = 1 := by sorry
