-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_col_base
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_base
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.771528+00:00
-- url     : https://prove2.me/theorems/4d09778e-3467-4b3c-878a-539815fb67e6
-- title:
--   A0: col base
-- statement:
--   The A0 construction uses the col base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L409-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L409-L437

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_base {N i : ℕ} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N) (hi : i ≤ N)
    (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : if last then m.val + 1 = n else m.val = 0) (J : Finset (Fin n)) :
    WGe isVec S last (sgn last)
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J))
      (sgn last * bc c (μ i m)) := by sorry
