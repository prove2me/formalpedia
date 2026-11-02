-- Prove2me | solution 1 for gpy_sum_primeInd_le_one
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T08:11:53.178168+00:00
-- url     : https://prove2.me/submissions/a0539ae9-187c-4fd7-9bf9-d6ee8a437c2c

/-
  Submission file for the Prove2Me problem `gpy_sum_primeInd_le_one` (PubAll batch, Oct 31, 2026).

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

def primeInd (m : ℕ) : ℝ := if Nat.Prime m then 1 else 0

/-- The linear GPY second moment: the prime sum over the tuple, weighted by
    the tuple weight, summed over the interval. -/

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

theorem sum_primeInd_le_one_restated_puball {k : ℕ} (h : Fin k → ℕ) (n : ℕ) (hat : ∀ i j : Fin k, i ≠ j → ¬ Nat.Prime (n + h i) ∨ ¬ Nat.Prime (n + h j)) : (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) ≤ 1 := by
  have hmain := sum_primeInd_le_one h n hat
  unfold primeInd at hmain
  exact hmain

end GPY

theorem solution {k : ℕ} (h : Fin k → ℕ) (n : ℕ) (hat : ∀ i j : Fin k, i ≠ j → ¬ Nat.Prime (n + h i) ∨ ¬ Nat.Prime (n + h j)) : (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) ≤ 1 := GPY.sum_primeInd_le_one_restated_puball h n hat
