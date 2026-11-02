-- Prove2me | solution 1 for gpy_exists_two_primes_of_secondMoment_gt
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T08:27:27.167708+00:00
-- url     : https://prove2.me/submissions/3091bdd3-bdb7-486a-b72e-cde0f0932649

/-
  Submission file for the Prove2Me problem `gpy_exists_two_primes_of_secondMoment_gt` (PubAll batch, Oct 31, 2026).

  Self-contained: imports Mathlib only. Contains the verified bodies
  of the dependency chain plus the restated theorem, with top-level
  `theorem solution` in the problem's exact binder/statement form.
  No sorry tactic, no axioms beyond the standard ones, no platform imports.
-/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

/-- Membership in the support set, unfolded. -/

noncomputable def weight (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ tupleSupport k R, if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2

/-- Weights are squares, hence nonnegative. -/

theorem weight_nonneg (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℕ) :
    0 ≤ weight k h R lam n := by
  unfold weight
  exact sq_nonneg _

/-- Diagonal expansion of the weight: the square of the sum is the double
    sum of pairwise products. This is the tuple analogue of the platform's
    λ² diagonalization. -/

def primeInd (m : ℕ) : ℝ := if Nat.Prime m then 1 else 0

/-- The linear GPY second moment: the prime sum over the tuple, weighted by
    the tuple weight, summed over the interval. -/

noncomputable def secondMoment (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc x y, (∑ i, primeInd (n + h i)) * weight k h R lam n

/-- The squared variant of the second moment (supporting lemma only): the
    square of the prime sum, weighted, summed over the interval. -/

theorem sum_primeInd_le_one {k : ℕ} (h : Fin k → ℕ) (n : ℕ)
    (hat : ∀ i j : Fin k, i ≠ j →
      ¬ Nat.Prime (n + h i) ∨ ¬ Nat.Prime (n + h j)) :
    (∑ i, primeInd (n + h i)) ≤ 1 := by
  classical
  have hcard : (Finset.univ.filter (fun i => Nat.Prime (n + h i))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    by_contra hab
    rcases hat a b hab with hna | hnb
    · exact hna ha.2
    · exact hnb hb.2
  have hsum : (∑ i, primeInd (n + h i))
      = ((Finset.univ.filter (fun i => Nat.Prime (n + h i))).card : ℝ) := by
    unfold primeInd
    rw [Finset.sum_boole]
  rw [hsum]
  exact_mod_cast hcard

/-- EXACT GPY CRITERION, per instance. If the linear second moment
    exceeds the first moment over the same interval, then some
    translate in the interval carries primes at two distinct
    coordinates. Proof: otherwise every translate has prime-count
    ≤ 1, and since the weight is nonnegative, S₂ ≤ S₁. -/

theorem exists_two_primes_of_secondMoment_gt {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ}
    (hgt : (∑ n ∈ Finset.Ioc x y, weight k h R lam n)
      < secondMoment k h R lam x y) :
    ∃ n ∈ Finset.Ioc x y, ∃ i j, i ≠ j ∧ Nat.Prime (n + h i)
      ∧ Nat.Prime (n + h j) := by
  classical
  by_contra hcon
  have hat : ∀ n ∈ Finset.Ioc x y, ∀ i j : Fin k, i ≠ j →
      ¬ Nat.Prime (n + h i) ∨ ¬ Nat.Prime (n + h j) := by
    intro n hn i j hij
    by_contra hnot
    push_neg at hnot
    exact hcon ⟨n, hn, i, j, hij, hnot.1, hnot.2⟩
  have hle : secondMoment k h R lam x y
      ≤ ∑ n ∈ Finset.Ioc x y, weight k h R lam n := by
    unfold secondMoment
    calc ∑ n ∈ Finset.Ioc x y, (∑ i, primeInd (n + h i)) * weight k h R lam n
        ≤ ∑ n ∈ Finset.Ioc x y, 1 * weight k h R lam n :=
          Finset.sum_le_sum (fun n hn =>
            mul_le_mul_of_nonneg_right (sum_primeInd_le_one h n (hat n hn))
              (weight_nonneg k h R lam n))
      _ = ∑ n ∈ Finset.Ioc x y, weight k h R lam n := by simp
  exact (not_le_of_gt hgt) hle

/-- Abstract threshold step: if S₁ is within E₁ of A and S₂ within E₂
    of B, and the main terms cross with room for both errors
    (A + E₁ < B - E₂), then S₂ > S₁ and the criterion applies. -/

theorem exists_two_primes_of_secondMoment_gt_restated_puball {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hgt : (∑ n ∈ Finset.Ioc x y, ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) < (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) * ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2))) : ∃ n ∈ Finset.Ioc x y, ∃ i j, i ≠ j ∧ Nat.Prime (n + h i) ∧ Nat.Prime (n + h j) := by
  exact exists_two_primes_of_secondMoment_gt h R lam hgt

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hgt : (∑ n ∈ Finset.Ioc x y, ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) < (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) * ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2))) : ∃ n ∈ Finset.Ioc x y, ∃ i j, i ≠ j ∧ Nat.Prime (n + h i) ∧ Nat.Prime (n + h j) := GPY.exists_two_primes_of_secondMoment_gt_restated_puball h R lam hgt
