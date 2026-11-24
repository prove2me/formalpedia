-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_good_smul_add
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.good_smul_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:18.061012+00:00
-- url     : https://prove2.me/theorems/9bdd7d3c-fe68-4d86-b194-2086b8ceb466
-- title:
--   Exponent Set Counting: good smul add
-- statement:
--   The Exponent Set Counting construction uses the good smul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L317-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L317-L330

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.good_smul_add (k : Type) [Field k] (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (c : k)
    (G H : MvPolynomial (ℕ × Fin n) k) (hG : GoodG isVec i θ M G) (hH : GoodG isVec i θ M H) :
    GoodG isVec i θ M (c • G + H) := by sorry
