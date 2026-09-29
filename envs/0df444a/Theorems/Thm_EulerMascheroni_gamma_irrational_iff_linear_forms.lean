-- Prove2me | Theorems.Thm_EulerMascheroni_gamma_irrational_iff_linear_forms
-- name    : EulerMascheroni.gamma_irrational_iff_linear_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T20:21:10.214856+00:00
-- url     : https://prove2.me/theorems/12c19c1e-d8dd-44b0-8f2b-8734babb03b6
-- title:
--   Irrationality of $\gamma$ is equivalent to the existence of vanishing linear forms
-- statement:
--   Euler's constant is irrational **if and only if** there exist integer sequences $(p_n)$ and $(q_n)$ whose linear forms
--
--   $$L_n \;=\; q_n \gamma - p_n$$
--
--   never vanish and satisfy $L_n \to 0$.
--
--   The backward direction is the classical irrationality criterion: if $\gamma = a/b$ then $bL_n$ is a non-zero integer, so $|L_n| \ge 1/b$ for every $n$, contradicting $L_n \to 0$.
--
--   The forward direction is Dirichlet's approximation theorem. For each $n$ it supplies a positive integer $k$ with $|k\gamma - \mathrm{round}(k\gamma)| \le 1/(n+2)$; taking $q_n = k$ and $p_n = \mathrm{round}(k\gamma)$ gives forms tending to zero, and they are non-zero precisely because $\gamma$ is irrational.
--
--   **Why the equivalence matters.** It converts the arithmetic question about a single real number into a construction problem about integers, and shows nothing is lost in the translation: a proof of irrationality *must* be obtainable in this shape. This is the interface every serious attack on the problem uses. Apery's proof of the irrationality of $\zeta(3)$ produces exactly such forms; the Pade-approximation constructions of Aptekarev and Rivoal produce them for the pair $(\gamma, \delta)$, but with decay too slow against the growth of $q_n$ to conclude for $\gamma$ alone — which is why those arguments yield only the disjunctive statements about the pair.
--
--   **Formalization note.** The forward direction uses Mathlib's `Real.exists_nat_abs_mul_sub_round_le`. Nothing in either direction is specific to $\gamma$ beyond its irrationality; the same equivalence holds for any real number, and it is stated here at $\gamma$ because that is where it is used.
-- source:
--   Classical: the irrationality criterion together with Dirichlet's approximation theorem. The criterion in this form is the one used throughout the literature on Euler's constant, e.g. A. I. Aptekarev, On linear forms containing the Euler constant, https://arxiv.org/abs/0902.1768.

import Mathlib

open Real

namespace EulerMascheroni

theorem gamma_irrational_iff_linear_forms :
    Irrational Real.eulerMascheroniConstant ↔
      ∃ p q : ℕ → ℤ,
        (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
        Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
          Filter.atTop (nhds 0) := by sorry

end EulerMascheroni
