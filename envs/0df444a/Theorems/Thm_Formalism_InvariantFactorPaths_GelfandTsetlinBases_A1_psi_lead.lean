-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psi_lead
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:56:01.918619+00:00
-- url     : https://prove2.me/theorems/4eab03bb-10cb-41da-b9a7-81c2d5116126
-- title:
--   A1: psi lead
-- statement:
--   The A1 construction uses the psi lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L591-L637
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L591-L637

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      LeadAt (wt n N (isVec N)) (rho n N (isVec N) (DD μ N))
        (psiPath R isVec μ (N + 1) (canIdx (μ (N + 1))))
        ((ε : MvPolynomial (ℕ × Fin n) R) * psiPath R isVec μ N (canIdx (μ N)) * monomial (DD μ N) 1) := by sorry
