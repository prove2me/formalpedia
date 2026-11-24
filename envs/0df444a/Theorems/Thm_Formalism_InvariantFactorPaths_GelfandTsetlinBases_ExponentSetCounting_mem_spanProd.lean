-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_mem_spanProd
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.mem_spanProd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:46.19386+00:00
-- url     : https://prove2.me/theorems/dc234a33-82bb-410a-a651-9abe4605d55c
-- title:
--   Exponent Set Counting: mem span Prod
-- statement:
--   The Exponent Set Counting construction uses the mem span Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L237-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/UnitAndFieldPowerLemmas.lean#L237-L260

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.mem_spanProd (hT : LemmaA3top) (hF : FactSplit) (k : Type) [Field k] (hn : 1 ≤ n) {i N : ℕ} (hi : i ≤ N)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ) (G : MvPolynomial (ℕ × Fin n) k)
    (hG : G ∈ polB k n N B) (hg : GoodG isVec i θ M G) :
    G ∈ Submodule.span k (Set.range (prodFam k n i N isVec B θ M)) := by sorry
