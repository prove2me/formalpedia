-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_glue_coordinate_split
-- name    : Formalism.FourierDecayAlt.P5.glue_coordinate_split
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:36.908589+00:00
-- url     : https://prove2.me/theorems/5387cb8b-a500-449d-8aef-148d02cc75bf
-- title:
--   P5: glue coordinate split
-- statement:
--   The P5 construction uses the glue coordinate split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L53-L69

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

theorem Formalism.FourierDecayAlt.P5.glue_coordinate_split (l : Fin r) (c : Fin r → ℂ) (a : Cf r l.castSucc) :
    glue l.castSucc c a = glue l.succ (Function.update c l (coordinateSplit l a).1) (coordinateSplit l a).2 := by sorry
