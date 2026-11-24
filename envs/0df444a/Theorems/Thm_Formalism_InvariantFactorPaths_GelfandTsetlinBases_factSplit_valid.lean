-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_factSplit_valid
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.factSplit_valid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:35.019872+00:00
-- url     : https://prove2.me/theorems/f5dd9b16-ec68-4db1-aafe-b8119db1c0a1
-- title:
--   Gelfand Tsetlin Bases: fact Split valid
-- statement:
--   The Gelfand Tsetlin Bases construction uses the fact Split valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L236-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/FactSplit.lean#L236-L270

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_FactSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open LowHighPartSplit

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.factSplit_valid : FactSplit := by sorry
