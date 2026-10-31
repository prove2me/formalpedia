-- Prove2me | solution 1 for gpy_prime_dvd_finset_prod
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:24:22.630164+00:00
-- url     : https://prove2.me/submissions/4e89e9b9-7359-4993-b4a9-9b3b9e86120a

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

theorem solution {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ ∏ i ∈ s, f i) : ∃ j ∈ s, p ∣ f j := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty] at h
    exact absurd h hp.not_dvd_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨j, hj, hjf⟩ := ih h2
      exact ⟨j, Finset.mem_insert_of_mem hj, hjf⟩

