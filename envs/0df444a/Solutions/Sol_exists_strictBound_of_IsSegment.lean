-- Prove2me | solution 1 for exists_strictBound_of_IsSegment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:46:02.040152+00:00
-- url     : https://prove2.me/submissions/0cb797ad-d92e-4e0b-bc29-22123932f098

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α]
theorem _root_.solution (S C : Set α) (hSC : S ⊏ C) (cha : IsChain (· ≤ ·) C) :
    ∃ sb ∈ C, ∀ a ∈ S, a < sb := by
  obtain ⟨c, hc⟩ := exists_of_ssubset <| ssubset_of_subset_of_ne hSC.1.1 hSC.2
  existsi c
  have : ∀ s ∈ S, s < c := by
    by_contra cle ; push Not at cle
    obtain ⟨s, hs⟩ := cle
    have comparable : s ≠ c → s ≤ c ∨ c ≤ s := cha (hSC.1.1 hs.1) hc.1
    by_cases s_eq_c : s = c
    · rw [s_eq_c] at hs ; tauto
    · have : s ≤ c → s < c ∨ s = c := LE.le.lt_or_eq
      have : c ≤ s → c ∈ S := hSC.1.2 c hc.1 s hs.1
      tauto
  exact ⟨hc.1, this⟩
