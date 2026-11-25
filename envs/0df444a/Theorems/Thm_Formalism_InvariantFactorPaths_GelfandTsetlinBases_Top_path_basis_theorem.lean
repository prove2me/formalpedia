-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Top_path_basis_theorem
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.path_basis_theorem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:04.235809+00:00
-- url     : https://prove2.me/theorems/d05ade7e-1093-46a3-b02b-fbcc8b053cf1
-- title:
--   Top: path basis theorem
-- statement:
--   The Top construction uses the path basis theorem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/PathBasisTheorem.lean#L21-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/PathBasisTheorem.lean#L21-L21

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.path_basis_theorem : PathBasisOfCount := by sorry
