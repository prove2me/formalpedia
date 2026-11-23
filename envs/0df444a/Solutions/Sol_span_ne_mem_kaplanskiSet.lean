-- Prove2me | solution 1 for span_ne_mem_kaplanskiSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:18:47.571452+00:00
-- url     : https://prove2.me/submissions/84ec7a5a-32a6-41e2-bd3e-fdf36027237e

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_mem_kaplanskySet_iff_inter_eq_empty
import Theorems.Thm_exists_mem_kaplanskySet_eq_of_le

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]
theorem _root_.solution {a : R} (ha : a ≠ 0)
      (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) :
    span {a} ∉ kaplanskySet (closure {r : R | Prime r}).toSubsemigroup := by
  have hzero : 0 ∉ closure {r : R | Prime r} := fun h ↦ by
    rcases exists_multiset_of_mem_closure h with ⟨l, hl, hprod⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_mem_kaplanskySet_eq_of_le hzero with ⟨T, hT, hT₂⟩
  have hT₃ : T ≠ ⊥ := fun h₂ ↦ ha (span_singleton_eq_bot.1 ((h₂ ▸ hT₂) _ h zero_le))
  have Tpri := isPrime_of_maximally_disjoint T _ hT (fun J hJ H ↦ hJ.ne (hT₂ J H hJ.le).symm)
  rcases (H T) hT₃ Tpri with ⟨x, H₃, H₄⟩
  rw [mem_kaplanskySet_iff_inter_eq_empty, eq_empty_iff_forall_notMem] at hT
  exact hT x ⟨H₃, subset_closure H₄⟩
