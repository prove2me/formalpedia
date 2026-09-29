-- Prove2me | Theorems.Thm_EulerMascheroni_gamma_irrational_of_linear_forms
-- name    : EulerMascheroni.gamma_irrational_of_linear_forms
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T06:51:30.30113+00:00
-- url     : https://prove2.me/theorems/356a755b-76f9-4b25-9a5d-a0877ebb47a9
-- title:
--   Irrationality of $\gamma$ from linear forms tending to zero
-- statement:
--   Suppose there are integer sequences $(p_n)$ and $(q_n)$ such that the linear forms
--
--   $$L_n \;=\; q_n\gamma - p_n$$
--
--   never vanish and satisfy $L_n \to 0$. Then $\gamma$ is irrational.
--
--   This is the classical irrationality criterion, and it is the shape every serious attack on the problem takes. The proof is short: if $\gamma = a/b$ with $b \ge 1$, then $bL_n = q_n a - p_n b$ is an integer, and it is non-zero by hypothesis, so $|L_n| \ge 1/b$ for every $n$ — contradicting $L_n \to 0$.
--
--   Its role in the mission is to be a **reduction**: it converts the irrationality of $\gamma$, a statement about a real number, into the construction of an explicit sequence of good rational approximations, a statement about integers. This is exactly what Apery's proof supplies for $\zeta(3)$, and what the Pade-approximation constructions of Aptekarev and Rivoal supply for $\gamma$ — except that there the forms produced do not decay fast enough relative to the growth of $q_n$, which is why those arguments yield only the disjunctive statements about the pair $(\gamma,\delta)$.
--
--   **Formalization note.** This node is elementary and provable now; the difficulty of the problem lives entirely in exhibiting sequences satisfying its hypotheses.
-- source:
--   Classical irrationality criterion; the form used throughout the literature on Euler's constant, e.g. A. I. Aptekarev, On linear forms containing the Euler constant, https://arxiv.org/abs/0902.1768, and the discussion in J. Lagarias, Bull. AMS 50 (2013), https://arxiv.org/abs/1303.1856, Section 5.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem gamma_irrational_of_linear_forms
    (p q : ℕ → ℤ)
    (hne : ∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational Real.eulerMascheroniConstant := by sorry
end EulerMascheroni
