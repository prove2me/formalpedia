-- Prove2me | solution 1 for gpy_coordOf_some_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T02:30:39.479049+00:00
-- url     : https://prove2.me/submissions/b2eb835a-9f70-407b-a192-b787ce69e052

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

theorem prime_dvd_finset_prod_aux {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
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

theorem pairwise_coprime_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ}
    (_hd1 : ∀ i, 1 ≤ d i) (hsq : Squarefree (∏ i, d i))
    {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by
  have hjerase : d j ∣ ∏ i' ∈ Finset.univ.erase i, d i' :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have hprod : ∏ i', d i' = d i * ∏ i' ∈ Finset.univ.erase i, d i' :=
    (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
  have hmul : d i * d j ∣ ∏ i', d i' := by
    rw [hprod]
    exact mul_dvd_mul_left (d i) hjerase
  have hg1 : Nat.gcd (d i) (d j) ∣ d i := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (d i) (d j) ∣ d j := Nat.gcd_dvd_right _ _
  have hgg : Nat.gcd (d i) (d j) * Nat.gcd (d i) (d j) ∣ ∏ i', d i' :=
    dvd_trans (mul_dvd_mul hg1 hg2) hmul
  have hu : IsUnit (Nat.gcd (d i) (d j)) := hsq _ hgg
  exact Nat.isUnit_iff.mp hu

theorem exists_unique_coord_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    (hpd : p ∣ ∏ j, d j) : ∃! j, p ∣ d j := by
  obtain ⟨j₀, -, hj₀⟩ := prime_dvd_finset_prod_aux hp hpd
  refine ⟨j₀, hj₀, ?_⟩
  intro y hy
  by_contra hne
  have hcop := pairwise_coprime_of_squarefree_prod_aux hd1 hsq hne
  have hdiv : p ∣ Nat.gcd (d y) (d j₀) := Nat.dvd_gcd hy hj₀
  have hgcd : Nat.gcd (d y) (d j₀) = 1 := hcop
  rw [hgcd] at hdiv
  exact hp.not_dvd_one hdiv

theorem coordOf_some_of_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    {j : Fin k} (hj : p ∣ d j) : coordOf d p = some j := by
  have hpd : p ∣ ∏ j, d j :=
    dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  obtain ⟨j₀, hj₀, huniq⟩ := exists_unique_coord_of_squarefree_prod_aux hd1 hsq hp hpd
  have hjj : j = j₀ := huniq j hj
  have hex : ∃ j', p ∣ d j' := ⟨j, hj⟩
  have hc : Classical.choose hex = j := by
    have h1 := Classical.choose_spec hex
    have h2 := huniq _ h1
    rw [← hjj] at h2
    exact h2
  unfold coordOf
  rw [dif_pos hex, hc]

theorem solution {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    {j : Fin k} (hj : p ∣ d j) :
    (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = some j :=
  coordOf_some_of_dvd_aux hd1 hsq hp hj
