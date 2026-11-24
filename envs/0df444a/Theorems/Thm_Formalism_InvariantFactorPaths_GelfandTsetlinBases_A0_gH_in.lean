-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_gH_in
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.gH_in
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:51.558369+00:00
-- url     : https://prove2.me/theorems/fed9595c-73b3-4009-b7b5-601d8f78c6e7
-- title:
--   A0: g H in
-- statement:
--   The A0 construction uses the g H in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L385-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L385-L401

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.gH_in {j : ℕ} (hj : j ∈ S) :
    (fun a : Fin n => gH k isVec S (X (j, a))) =
      if isVec j then
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n)) : Matrix (Fin n) (Fin n) _)
      else
        Matrix.vecMul (fun b => (X (Sum.inl (j, b)) : MvPolynomial (LVar ℕ Empty n) (GenField k n)))
          (↑(gam k n (LVar ℕ Empty n))⁻¹ : Matrix (Fin n) (Fin n) _).transpose := by sorry
