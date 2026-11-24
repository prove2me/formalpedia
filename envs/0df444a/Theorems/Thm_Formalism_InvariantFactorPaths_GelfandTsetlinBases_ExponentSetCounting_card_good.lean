-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_card_good
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.card_good
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:12.598463+00:00
-- url     : https://prove2.me/theorems/fe42a0b2-c8e8-42c9-ac3d-f50569b6f8b1
-- title:
--   Exponent Set Counting: card good
-- statement:
--   The Exponent Set Counting construction uses the card good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L112-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L112-L154

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.card_good (hC : CountCont) {i N : ℕ} (hi : i ≤ N) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ)
    (M : WithTop ℤ) :
    Nat.card {x : PathIdx n N isVec B // GoodW θ M (x.1.1 i)} =
      Nat.card {x : PathIdx n i isVec B // GoodW θ M (x.1.1 i)} *
        ∏ l ∈ Finset.Ico i N, (n + B l - 1).choose (B l) := by sorry
