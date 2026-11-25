-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_sum
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.sum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:16:19.307896+00:00
-- url     : https://prove2.me/theorems/6ae10096-9ab7-43ea-a969-8786db18e389
-- title:
--   Meas: sum
-- statement:
--   The Meas construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L112-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L112-L127

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

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.sum (h : Meas dx φ J g) {F : G → ℂ} (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : ℂ} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0) :
    (∑ᶠ z : G ⧸ J, F z.out) * ((dx (φ '' stab J g)).toReal : ℂ) = y * ((dx (φ '' A)).toReal : ℂ) := by sorry
