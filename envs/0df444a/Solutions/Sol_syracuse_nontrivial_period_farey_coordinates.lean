-- Prove2me | solution 1 for syracuse_nontrivial_period_farey_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-24T10:12:53.476806+00:00
-- url     : https://prove2.me/submissions/e785dc27-a298-46be-a1b3-4a61f2398047

import Theorems.Thm_syracuse_nontrivial_cycle_dyadic_exponent_bound
import Theorems.Thm_syracuse_cycle_pow_two_gt_pow_three

/- Compare powers by clearing rational exponents. -/
private theorem transposePowers (a i j : ℕ) : (a ^ i) ^ j = (a ^ j) ^ i := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm i j]

set_option exponentiation.threshold 150000 in
private theorem exponentLower (p K : ℕ) (hp : 0 < p) (hg : 3 ^ p < 2 ^ K) :
    50508 * p < 31867 * K := by
  have hfixed : (2 : ℕ) ^ 50508 < 3 ^ 31867 := by decide +kernel
  have h : (2 : ℕ) ^ (50508 * p) < 2 ^ (31867 * K) := by
    calc
      (2 : ℕ) ^ (50508 * p) = (2 ^ 50508) ^ p := Nat.pow_mul _ _ _
      _ < (3 ^ 31867) ^ p :=
        Nat.pow_lt_pow_left (n := p) hfixed (Nat.ne_of_gt hp)
      _ = (3 ^ p) ^ 31867 := transposePowers _ _ _
      _ < (2 ^ K) ^ 31867 := Nat.pow_lt_pow_left (n := 31867) hg (by decide)
      _ = 2 ^ (31867 * K) := by rw [← Nat.pow_mul, Nat.mul_comm K]
  exact Nat.lt_of_not_ge fun hbad => Nat.not_le_of_gt h (Nat.pow_le_pow_right (by decide) hbad)

theorem solution (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 665*a + 10946*b ∧ K = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 2*b ≤ 13*a := by
  dsimp only
  let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
  have low : 50508*p < 31867*K := exponentLower p K hp
    (syracuse_cycle_pow_two_gt_pow_three m p hm hp hcycle)
  have high : 143628*K ≤ 227645*p :=
    syracuse_nontrivial_cycle_dyadic_exponent_bound m p hm hp hcycle hne
  let a := 17349*p - 10946*K
  let b := 665*K - 1054*p
  have ha : 10946*K < 17349*p := by omega
  have hb : 1054*p < 665*K := by omega
  refine ⟨a, b, Nat.sub_pos_of_lt ha, Nat.sub_pos_of_lt hb, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only [a,b]; omega
