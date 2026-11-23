-- Prove2me | solution 1 for uniqueFactorizationMonoid_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:21:45.973577+00:00
-- url     : https://prove2.me/submissions/39c3ea64-50b3-4f25-8613-9cb2843162b6

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_uniqueFactorizationMonoid_of_exists_prime

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [CommSemiring R] [IsDomain R]
theorem _root_.solution :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x :=
  ⟨fun _ _ hI hI₂ ↦ hI₂.exists_mem_prime_of_ne_bot hI,
    fun H ↦ uniqueFactorizationMonoid_of_exists_prime H⟩
