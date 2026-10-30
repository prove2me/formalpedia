-- Prove2me | solution 1 for gpy_combined_lcm_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:27:21.005401+00:00
-- url     : https://prove2.me/submissions/a65a344b-a316-4e8c-b920-b506555e988b

/- Submission file for the Prove2Me problem `gpy_combined_lcm_eq` (publish2 fiber batch).
   Self-contained: imports Mathlib only. Contains the verified helper
   bodies needed for the proof, with top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

/-- On squarefree-product support the coordinates are pairwise
    coprime: the gcd of two distinct coordinates squares-divides
    the product, and squarefree forces it to be `1`. -/
theorem pairwise_coprime_of_squarefree_prod {k : ℕ} {d : Fin k → ℕ}
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

/-- If a family is pairwise coprime and every coordinate divides `L`,
    then the product divides `L` (induction on the tuple dimension). -/
theorem prod_dvd_of_pairwise_coprime :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := by
  intro k
  induction k with
  | zero =>
    intro d L _ _
    simp
  | succ k ih =>
    intro d L hcop hdvd
    rw [Fin.prod_univ_succ]
    have hcop_tail : ∀ i j, i ≠ j → Nat.Coprime (Fin.tail d i) (Fin.tail d j) :=
      fun i j hij => hcop i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
    have hdvd_tail : ∀ i, Fin.tail d i ∣ L := fun i => hdvd i.succ
    have htail : ∏ i, Fin.tail d i ∣ L := ih hcop_tail hdvd_tail
    have hcop0 : Nat.Coprime (d 0) (∏ i, Fin.tail d i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i _
      exact hcop 0 i.succ (Fin.succ_ne_zero i).symm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop0 (hdvd 0) htail

/-- On squarefree-product support, the combined modulus
    `Finset.lcm univ (fun j => Nat.lcm (d j) (e j))` equals
    `Nat.lcm (∏ d) (∏ e)`. -/
theorem combined_lcm_eq {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := by
  apply dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    apply Nat.lcm_dvd
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · apply prod_dvd_of_pairwise_coprime
        (fun i j hij => pairwise_coprime_of_squarefree_prod hd1 hsqd hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_left (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))
    · apply prod_dvd_of_pairwise_coprime
        (fun i j hij => pairwise_coprime_of_squarefree_prod he1 hsqe hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_right (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))


end GPY

theorem solution {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := GPY.combined_lcm_eq hd1 he1 hsqd hsqe
