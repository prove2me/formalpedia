-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_sum_Dc
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.sum_Dc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:45.061433+00:00
-- url     : https://prove2.me/theorems/d67bee1d-5855-4833-a4ce-608825812b59
-- title:
--   A1: sum Dc
-- statement:
--   The A1 construction uses the sum Dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L562-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L562-L584

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.sum_Dc {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (S : Finset ℤ)
    (hS : ∀ c, colHeight (μ (N + 1)) c ≠ colHeight (μ N) c → c ∈ S) :
    ∑ c ∈ S, Dc μ N c = DD μ N := by sorry
