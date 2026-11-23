-- Prove2me | solution 1 for exists_mem_kaplanskySet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:14:47.337709+00:00
-- url     : https://prove2.me/submissions/cfd22000-5b15-4a95-83a3-8e14b7cc5b87

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_mem_kaplanskySet_iff_inter_eq_empty

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}
theorem _root_.solution {C : Set (Ideal R)} (hS : 0 ∉ S) (hC : C ⊆ kaplanskySet S)
      (hC₂ : IsChain (· ≤ ·) C) : ∃ P ∈ kaplanskySet S, ∀ J ∈ C, J ≤ P := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨_, hI⟩
  · exact ⟨⊥, by simpa [mem_kaplanskySet_iff_inter_eq_empty, eq_empty_iff_forall_notMem]⟩
  · refine ⟨sSup C, ?_, fun _ hz ↦ le_sSup hz⟩
    rw [mem_kaplanskySet_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
    intro x hx
    rcases (Submodule.mem_sSup_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
    have hx₂ : (J : Set R) ∩ S ≠ ∅ := nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
    exact hx₂ (mem_kaplanskySet_iff_inter_eq_empty.mp (hC hJ₁))
