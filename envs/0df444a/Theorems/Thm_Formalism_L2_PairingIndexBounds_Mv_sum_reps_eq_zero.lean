-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_sum_reps_eq_zero
-- name    : Formalism.L2.PairingIndexBounds.Mv.sum_reps_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:46.649819+00:00
-- url     : https://prove2.me/theorems/6f685b8d-fa36-4cbf-9ad6-999d46836aed
-- title:
--   Mv: sum reps eq zero
-- statement:
--   The Mv construction uses the sum reps eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L48-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L48-L87

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
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
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

theorem Formalism.L2.PairingIndexBounds.Mv.sum_reps_eq_zero {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S)
    (f : G → k) (hadd : ∀ x y, f (x + y) = f x * f y) (hM : ∀ x ∈ M, f x = 1) (g₀ : G) (hg₀ : g₀ ∈ N)
    (hne : f g₀ ≠ 1) : ∑ x ∈ S, f x = 0 := by sorry
