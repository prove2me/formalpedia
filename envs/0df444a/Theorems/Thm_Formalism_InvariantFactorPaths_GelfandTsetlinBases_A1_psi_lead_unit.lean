-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_psi_lead_unit
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:46.656552+00:00
-- url     : https://prove2.me/theorems/0b0bdafe-47e9-4de3-ba41-7538247705dc
-- title:
--   A1: psi lead unit
-- statement:
--   The A1 construction uses the psi lead unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L735-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L735-L744

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.psi_lead_unit (k : Type) [Field k] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    (hp : IsPath n isVec B μ (N + 1)) :
    ∃ u : kˣ, weightedHomogeneousComponent (wt n N (isVec N)) (rho n N (isVec N) (DD μ N))
        (psiPath k isVec μ (N + 1) (canIdx (μ (N + 1)))) =
      u • (psiPath k isVec μ N (canIdx (μ N)) * monomial (DD μ N) 1) := by sorry
