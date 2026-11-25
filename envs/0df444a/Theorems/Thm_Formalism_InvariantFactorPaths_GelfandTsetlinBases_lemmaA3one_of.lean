-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lemmaA3one_of
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lemmaA3one_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:03.832289+00:00
-- url     : https://prove2.me/theorems/9011c4fd-1bc7-4e29-afec-b39d8edd6c30
-- title:
--   Gelfand Tsetlin Bases: lemma A3one of
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lemma A3one of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L384-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L384-L386

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lemmaA3one_of : LemmaA2indep → PathIdxFinite → PolBRank → LemmaA3top → FactSplit → CountCont →
    StdCountGT → LemmaA3one := by sorry
