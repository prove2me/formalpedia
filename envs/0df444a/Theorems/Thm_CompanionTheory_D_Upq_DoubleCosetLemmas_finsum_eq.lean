-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_finsum_eq
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.finsum_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:36.207232+00:00
-- url     : https://prove2.me/theorems/f143ead8-15fa-4d12-9eea-6c92408e709b
-- title:
--   Double Coset Lemmas: finsum eq
-- statement:
--   The Double Coset Lemmas construction uses the finsum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L92-L108

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.DoubleCosetLemmas
variable {G M : Type} [Group G] [MeasurableSpace M]
variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}
open Classical

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.finsum_eq (hf : (cos J g J).Finite) (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : Y} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ∑ᶠ z : G ⧸ J, F z.out = ((cos J g A).ncard : ℂ) • y := by sorry
