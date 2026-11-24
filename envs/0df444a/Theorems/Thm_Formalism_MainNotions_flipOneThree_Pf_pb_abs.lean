-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_pb_abs
-- name    : Formalism.MainNotions.flipOneThree.Pf.pb_abs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:31.964082+00:00
-- url     : https://prove2.me/theorems/175deca9-706a-4aa4-a4fc-d8fefe6d37a0
-- title:
--   Pf: pb abs
-- statement:
--   The Pf construction uses the pb abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/HermitianTensor/GrowthOfBasic.lean#L9-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/HermitianTensor/GrowthOfBasic.lean#L9-L241

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_GrowthOfBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Submodule

theorem Formalism.MainNotions.flipOneThree.Pf.pb_abs {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (w π : O) (hw : Irreducible w) (hπ : w ^ 2 = π) (N n : ℕ) (b : Fin n → V) (hli : LinearIndependent K b)
    (B0 : V →ₗ[K] V →ₗ[K] K)
    (hb : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span K (Set.range b), B0 P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ span K (Set.range b), (∀ P ∈ span O (Set.range b), B0 P Q ∈ Set.range (algebraMap O K)) →
      Q ∈ span O (Set.range b))
    (hd : ∀ Q ∈ span O (Set.range b), ∀ P ∈ span O (Set.range b),
      B0 P ((algebraMap O K π ^ N) • Q) ∈ Set.range (algebraMap O K)) :
    ∃ (x x' : Fin n → V) (ka : Fin n → ℕ), (∀ i, ka i ≤ N) ∧ (∀ i, x i ∈ span O (Set.range b)) ∧
      (∀ i, x' i ∈ span O (Set.range b)) ∧
      ∀ a' i, algebraMap O K π ^ N * B0 (x i) (x' a') = if a' = i then algebraMap O K π ^ ka i else 0 := by sorry
