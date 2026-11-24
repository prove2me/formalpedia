-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_col_all
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_all
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:35.032409+00:00
-- url     : https://prove2.me/theorems/4d0bb973-2157-493b-ad29-e31cb7f8b28f
-- title:
--   A0: col all
-- statement:
--   The A0 construction uses the col all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L439-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L439-L472

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.col_all {i : ℕ} {μ : ℕ → Fin n → ℤ} (hS : ∀ j, j ∈ S ↔ j < i) (c : ℤ) (last : Bool) (s a : ℤ)
    (h0 : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) i J)) a)
    (N : ℕ) (hN : i ≤ N) : ∀ J : Finset (Fin n), WGe isVec S last s
      (gH k isVec S (pathWord isVec μ c (fun j a => (X (j, a) : MvPolynomial (ℕ × Fin n) k)) N J)) a := by sorry
