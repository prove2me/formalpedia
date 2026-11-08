-- Prove2me | Theorems.Thm_Eliahou1993_rational_linear_form
-- name    : Eliahou1993.rational_linear_form
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T14:38:49.074431+00:00
-- url     : https://prove2.me/theorems/56e2d0eb-9098-4869-b4e3-602d014347be
-- title:
--   Eliahou (1993) Theorem 1.1 (rational form): conditional linear form for numerators in $(\log_2 3, \log_2(3+1/m)]$
-- statement:
--   Let $k_1, L, m \in \mathbb{N}$ be natural numbers with $k_1 > 0$ and $m > 2^{40}$. If the fraction $L / k_1$ satisfies $\log_2 3 < L / k_1 \le \log_2(3 + 1/m)$, then there exist nonnegative integers $a, b, c \in \mathbb{N}$ such that
--
--   $$
--   b > 0, \quad a c = 0, \quad \text{and} \quad L = 301{,}994\, a + 17{,}087{,}915\, b + 85{,}137{,}581\, c.
--   $$
--
--   This theorem establishes the arithmetic core of Eliahou's Theorem 1.1: any rational number $L / k_1$ in the interval $(\log_2 3, \log_2(3 + 1/m)]$ with $m > 2^{40}$ lies in one of the two adjacent Farey intervals $(p_{16}/q_{16}, p_{15}/q_{15}]$ or $[p_{15}/q_{15}, p_{13}/q_{13})$ where $p_{13} = 301{,}994$, $p_{15} = 17{,}087{,}915$, and $p_{16} = 85{,}137{,}581$.
--
--   **Formalization Note** This theorem is **conditional** on the explicit hypothesis $2^{40} < m$ (`(2 : ℕ) ^ 40 < m`), which is assumed as an input parameter and not certified on the platform. Stated in the `Eliahou1993` namespace (`Eliahou1993.rational_linear_form`). Adapted under the MIT License from `tangentproofs/eliahou-collatz-bounds` (commit `18cc351df2f942ddba4bf03feb9b75a70701497d`, Copyright (c) 2026 Michal Wallace; co-authored by Aristotle / Harmonic).
-- source:
--   Shalom Eliahou (1993), 'The 3x + 1 problem: new lower bounds on nontrivial cycle lengths', Discrete Mathematics 118(1-3), pp. 45–56, pp. 46, 50–51, Theorem 1.1; https://github.com/tangentproofs/eliahou-collatz-bounds/blob/18cc351df2f942ddba4bf03feb9b75a70701497d/Collatz/LinearForm.lean#L127-L168 (Adapted from tangentproofs/eliahou-collatz-bounds (commit 18cc351df2f942ddba4bf03feb9b75a70701497d, Copyright (c) 2026 Michal Wallace, MIT License; co-authored by Aristotle / Harmonic).)

/-
Adapted from https://github.com/tangentproofs/eliahou-collatz-bounds
(commit 18cc351df2f942ddba4bf03feb9b75a70701497d, file Collatz/LinearForm.lean),
formalizing:
  Shalom Eliahou (1993), "The 3x + 1 problem: new lower bounds on nontrivial
  cycle lengths", Discrete Mathematics 118(1-3), pp. 45–56, Theorem 1.1.
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

MIT License — Copyright (c) 2026 Michal Wallace. See Definitions/Def_eliahou1993Cycle.lean for full notice.
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Real

theorem Eliahou1993.rational_linear_form {k₁ L : ℕ} (hk₁ : 0 < k₁)
    {m : ℕ} (hm : 2 ^ 40 < m)
    (hlower : Real.logb 2 3 < (L : ℝ) / k₁)
    (hupper : (L : ℝ) / k₁ ≤ Real.logb 2 (3 + 1 / (m : ℝ))) :
    ∃ (a b c : ℕ), 0 < b ∧ a * c = 0 ∧
      L = 301994 * a + 17087915 * b + 85137581 * c := by sorry
