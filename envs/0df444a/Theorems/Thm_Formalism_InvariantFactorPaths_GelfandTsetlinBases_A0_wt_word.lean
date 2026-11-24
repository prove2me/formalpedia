-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wt_word
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wt_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:14.260737+00:00
-- url     : https://prove2.me/theorems/c802492c-8b83-443e-b9f6-519f70147350
-- title:
--   A0: wt word
-- statement:
--   The A0 construction uses the wt word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L296-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ValuationProductsComponents.lean#L296-L323

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wt_word {L : Type*} [CommRing L] {n i : ℕ} (isVec : ℕ → Bool) (S : Set ℕ) [DecidablePred (· ∈ S)]
    (hS : ∀ j, j < i → j ∈ S) (μ : ℕ → Fin n → ℤ) (c : ℤ) (last : Bool) (m : Fin n)
    (hm : ∀ a : Fin n, (if last then a.val + 1 = n else a.val = 0) ↔ a = m) :
    ∀ j ≤ i, ∀ J : Finset (Fin n), IsWeightedHomogeneous (wtX (ζ := Empty) isVec S last)
      (pathWord isVec μ c (fun l a => (X (Sum.inl (l, a)) : MvPolynomial (LVar ℕ Empty n) L)) j J)
      (if m ∈ J then (if 1 ≤ c then 1 else -1) else 0) := by sorry
