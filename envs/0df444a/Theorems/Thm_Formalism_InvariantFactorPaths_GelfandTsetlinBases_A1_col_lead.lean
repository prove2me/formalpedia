-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_col_lead
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.col_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:25.145961+00:00
-- url     : https://prove2.me/theorems/71dc4e77-f55f-4503-894a-3fcdc236c170
-- title:
--   A1: col lead
-- statement:
--   The A1 construction uses the col lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L349-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L349-L500

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.col_lead (R : Type*) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) (c : ℤ) :
    ∃ a : ℤ, (a = 1 ∨ a = -1) ∧
      LeadAt (wt n N (isVec N)) (Finsupp.weight (wt n N (isVec N)) (Dc μ N c))
        (pathWord isVec μ c (XR R n) (N + 1) (canIdx (μ (N + 1)) c))
        ((a : MvPolynomial (ℕ × Fin n) R) * pathWord isVec μ c (XR R n) N (canIdx (μ N) c) *
          monomial (Dc μ N c) 1) := by sorry
