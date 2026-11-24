-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_psi_bound
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.psi_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:50.035485+00:00
-- url     : https://prove2.me/theorems/d337b804-1487-43ca-a4e2-656852e090cf
-- title:
--   A0: psi bound
-- statement:
--   The A0 construction uses the psi bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L474-L494
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L474-L494

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable (k : Type) [Field k] {n : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
variable {k isVec S}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.psi_bound {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} {I : ℤ → Finset (Fin n)}
    (hp : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) :
    WGe isVec S last (sgn last) (gH k isVec S (psiPath k isVec μ N I)) (sgn last * μ i m) := by sorry
