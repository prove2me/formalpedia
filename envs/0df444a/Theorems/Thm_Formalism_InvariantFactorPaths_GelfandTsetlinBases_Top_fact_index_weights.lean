-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_fact_index_weights
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.fact_index_weights
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:07.148616+00:00
-- url     : https://prove2.me/theorems/f8473cef-7787-4534-9298-aff29126591b
-- title:
--   Top: fact index weights
-- statement:
--   The Top construction uses the fact index weights property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/PathBasisTheorem.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/PathBasisTheorem.lean#L15-L15

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_FinalP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_PathBasisTheorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.fact_index_weights : IndexWeightsDominance := by sorry
