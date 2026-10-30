-- Prove2me | solution 1 for gpy_prod_dvd_of_pairwise_coprime
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:27:19.789863+00:00
-- url     : https://prove2.me/submissions/328c39ab-f315-48c7-ab1a-8b0d7eb23d77

/- Submission file for the Prove2Me problem `gpy_prod_dvd_of_pairwise_coprime` (publish2 fiber batch).
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


end GPY

theorem solution :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := GPY.prod_dvd_of_pairwise_coprime
