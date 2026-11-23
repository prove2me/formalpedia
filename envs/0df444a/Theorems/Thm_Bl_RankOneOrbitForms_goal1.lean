-- Prove2me | Theorems.Thm_Bl_RankOneOrbitForms_goal1
-- name    : Bl.RankOneOrbitForms.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:46.594769+00:00
-- url     : https://prove2.me/theorems/e3e317c0-f662-4951-aaae-42d01d0c1aea
-- title:
--   Rank One Orbit Forms: goal1
-- statement:
--   The Rank One Orbit Forms construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/RankOneOrbitForms/RankOneForm.lean#L88-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/RankOneOrbitForms/RankOneForm.lean#L88-L170

import Mathlib
import Definitions.Def_Lemmata_RankOneOrbitForms_RankOneForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open Bl Bl.RankOneOrbitForms
variable {K : Type} [Field K] {G : Type} [Group G] {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem Bl.RankOneOrbitForms.goal1 (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by sorry
