-- Prove2me | Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_out_eq
-- name    : CompanionTheory.D.Upq.DoubleCosetLemmas.out_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:42.248677+00:00
-- url     : https://prove2.me/theorems/fe3e4b7b-a968-45b4-91df-51697bb10e64
-- title:
--   Double Coset Lemmas: out eq
-- statement:
--   The Double Coset Lemmas construction uses the out eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean#L79-L81

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

theorem CompanionTheory.D.Upq.DoubleCosetLemmas.out_eq (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z) (x : G) : F ((x : G ⧸ J).out) = F x := by sorry
