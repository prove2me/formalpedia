-- Prove2me | solution 1 for markov_brothers_integer_grid
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-05-09T00:51:05.957362+00:00
-- url     : https://prove2.me/submissions/fa95d7bb-67a3-405f-bf08-7757933423cc

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Real.Basic

/-!
# Markov's brothers inequality on the integer grid

A univariate real polynomial of degree `≤ d` whose absolute value is at most
`1` on the integer grid `{0, 1, …, b}` admits a derivative bound of the form
`|p'(c)| ≤ 2 d² / b` everywhere on the continuous interval `[0, b]`.

Proof outline (NOT formalised here):
1. **Ehlich–Zeller / Coppersmith–Rivlin (1992):** integer-grid bound `M`
   on `{0, …, b}` extends to a continuous bound `≤ 2 M` on `[0, b]`
   (provided `d² ≤ b`; else the bound is vacuous, but the conclusion still
   holds because `2 d² / b ≥ 2`).
2. **Classical Markov's inequality on `[0, b]`:** `|p'(x)| ≤ d² · M_cont · 2 / b`
   for `x ∈ [0, b]`, where `M_cont` is the continuous max bound from step 1.
3. Combine: `|p'(x)| ≤ 2 d² / b`.

Left as a platform leaf — DEFERRED. Likely needs further sub-decomposition
into (a) Ehlich–Zeller continuous extension and (b) classical Markov on an
interval, in a follow-up planning session focused on this leaf alone.
-/


open Polynomial

/-- Disproof of `markov_brothers_integer_grid`.

Counterexample: `b = 1`, `Q = 10·X² − 10·X`, `d = 2`, `c = 0`.
Then `Q(0) = Q(1) = 0` so the grid bound `|Q(t)| ≤ 1` holds, and
`natDegree Q = 2 ≤ 2`, but `Q'(x) = 20X − 10` so `|Q'(0)| = 10 > 8 = 2·d²/b`.

The theorem is false because the hypothesis only controls `Q` at the integer
grid points, which does not pin down its behavior between grid points when
`d` exceeds the number of grid intervals. -/
theorem solution : ¬ (∀
    {b : ℕ} (hb : 1 ≤ b) (Q : Polynomial ℝ) {d : ℕ}
    (h_deg : Q.natDegree ≤ d)
    (h_bound : ∀ t : ℕ, t ≤ b → |Q.eval (t : ℝ)| ≤ 1),
    ∀ c : ℝ, 0 ≤ c → c ≤ (b : ℝ) →
      |Q.derivative.eval c| ≤ 2 * (d : ℝ)^2 / (b : ℝ)) := by
  intro h
  -- Apply h at b = 1, Q = C 10 * X^2 - C 10 * X, d = 2, c = 0.
  have key := @h 1 (le_refl 1) (C (10 : ℝ) * X ^ 2 - C (10 : ℝ) * X) 2
    (by compute_degree)
    (by
      intro t ht
      interval_cases t <;>
        simp only [Nat.cast_zero, Nat.cast_one, eval_sub, eval_mul, eval_C, eval_pow, eval_X] <;>
        norm_num)
    0 le_rfl (by norm_num)
  -- key : |derivative (C 10 * X^2 - C 10 * X) .eval 0| ≤ 2 * (2:ℝ)^2 / (1:ℝ)
  -- derivative = C 10 * (C 2 * X) - C 10 * 1 = C 20 * X - C 10, eval at 0 = -10
  simp only [derivative_sub, derivative_C_mul, derivative_X_pow, derivative_X,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one,
    Nat.cast_ofNat, Nat.cast_one, pow_one, mul_one, mul_zero, zero_sub] at key
  -- key : |(-10 : ℝ)| ≤ 2 * 2 ^ 2 / 1
  norm_num at key
