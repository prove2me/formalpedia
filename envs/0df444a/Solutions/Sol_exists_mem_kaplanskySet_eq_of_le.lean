-- Prove2me | solution 1 for exists_mem_kaplanskySet_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:17:03.306176+00:00
-- url     : https://prove2.me/submissions/a945372e-bc0c-439b-b500-184fb2b0f16c

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
import Theorems.Thm_exists_mem_kaplanskySet_le

set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}
theorem _root_.solution (hS : 0 ∉ S) :
    ∃ P ∈ kaplanskySet S, ∀ I ∈ kaplanskySet S, P ≤ I → I = P := by
  obtain ⟨P, hP⟩ := zorn_le₀ (kaplanskySet S) (fun _ ↦ exists_mem_kaplanskySet_le hS)
  exact ⟨P, hP.1, fun _ hI H ↦ le_antisymm (hP.2 hI H) H⟩
