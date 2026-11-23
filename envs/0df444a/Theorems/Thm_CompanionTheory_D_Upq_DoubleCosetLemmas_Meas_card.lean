-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_card
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:02.275847+00:00
-- url     : https://prove2.me/theorems/f5d76482-9fa5-40a6-9336-72a3322b6063
-- title:
--   Meas: card
-- statement:
--   The Meas construction uses the card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L61-L73

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

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.card (h : Meas dx φ J g) {A : Set G} (hA : A ⊆ J)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ((cos J g A).ncard : ENNReal) * dx (φ '' stab J g) = dx (φ '' A) := by sorry
