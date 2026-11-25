-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_psiFam_good
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.psiFam_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:56.780271+00:00
-- url     : https://prove2.me/theorems/0f30f72c-fa5c-4b24-bf4e-da1448769d56
-- title:
--   Exponent Set Counting: psi Fam good
-- statement:
--   The Exponent Set Counting construction uses the psi Fam good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L217-L231

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.psiFam_good (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ)
    (θ : WithBot ℤ) (M : WithTop ℤ) (x : PathIdx n N isVec B) (hx : GoodW θ M (x.1.1 i)) :
    GoodG isVec i θ M (psiFam k n N isVec B x) := by sorry
