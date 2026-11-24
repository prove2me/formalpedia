-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P5_coordinate_split_snd
-- name    : Formalism.FourierDecayAlt.P5.coordinate_split_snd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:08:24.512083+00:00
-- url     : https://prove2.me/theorems/0d5887e8-b9cb-4266-856c-618e65e30561
-- title:
--   P5: coordinate split snd
-- statement:
--   The P5 construction uses the coordinate split snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelIntegrandAestronglyMeasurable.lean#L49-L51

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

theorem Formalism.FourierDecayAlt.P5.coordinate_split_snd (l : Fin r) (a : Cf r l.castSucc) (j : {j : Fin r // l.succ.val ≤ j.val}) :
    (coordinateSplit l a).2 j = a ⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩ := by sorry
