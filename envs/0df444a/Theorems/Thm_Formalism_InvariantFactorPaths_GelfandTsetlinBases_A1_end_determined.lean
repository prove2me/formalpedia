-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_end_determined
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.end_determined
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:52.697851+00:00
-- url     : https://prove2.me/theorems/597d890c-765e-4b63-8216-add4b938d5c1
-- title:
--   A1: end determined
-- statement:
--   The A1 construction uses the end determined property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L709-L733
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L709-L733

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.end_determined {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ μ' : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (hp' : IsPath n isVec B μ' (N + 1)) (he : μ (N + 1) = μ' (N + 1))
    (v : Bool) (hΓ : rho n N v (DD μ N) = rho n N v (DD μ' N)) : μ N = μ' N := by sorry
