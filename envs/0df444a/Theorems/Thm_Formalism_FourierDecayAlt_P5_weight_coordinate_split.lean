-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_weight_coordinate_split
-- name    : Formalism.FourierDecayAlt.P5.weight_coordinate_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:05.888668+00:00
-- url     : https://prove2.me/theorems/6b8794d9-1cd5-4bec-b382-e55d8245a52e
-- title:
--   P5: weight coordinate split
-- statement:
--   The P5 construction uses the weight coordinate split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L71-L78

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

theorem Formalism.FourierDecayAlt.P5.weight_coordinate_split (l : Fin r) (a : Cf r l.castSucc) :
    (∏ j, ‖a j‖ ^ (-2 : ℤ)) = ‖(coordinateSplit l a).1‖ ^ (-2 : ℤ) * ∏ j, ‖(coordinateSplit l a).2 j‖ ^ (-2 : ℤ) := by sorry
