-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_iterIntMinus_le_pow_div_factorial
-- name    : AntonelliBFSDE.Backward.iterIntMinus_le_pow_div_factorial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:25.066776+00:00
-- url     : https://prove2.me/theorems/4985befd-ad3e-47f7-8709-d7e7daf5d345
-- title:
--   Proof of Theorem 2.4, p. 783 — $A_t^{(n-)}\le A_t^n/n!$
-- statement:
--   Let $a:[0,\infty)\to\mathbb R$ be nondecreasing and right-continuous with $a_0=0$, and let $a^{(n-)}$ be its iterated Lebesgue–Stieltjes integral with left limits, $a^{(0-)}=1$, $a^{((n+1)-)}_t=\int_{(0,t]}a^{(n-)}_{s-}\,da_s$. Then for every $n\ge0$ and $t\ge0$,
--   $$a_t^{(n-)}\le\frac{a_t^{\,n}}{n!}.$$
--   Equality holds when $a$ is continuous; jumps only decrease the left side.
--
--   Applied to the integrator $A$ with $A_T\le\beta$, this turns (2.8) into the bound $k^n\beta^n/n!$.
--
--   **Formalization Note** Stated for a deterministic path, as it is used pathwise.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 783, proof of Theorem 2.4

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Proof of Theorem 2.4, p. 783: for a nondecreasing right-continuous path `a` with `a(0) = 0`,
`a_t^{(n-)} ≤ a_t^n / n!` for every `n` and every `t`. -/
theorem iterIntMinus_le_pow_div_factorial (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (t : ℝ≥0) :
    iterIntMinus a n t ≤ a t ^ n / (n.factorial : ℝ) := by sorry

end AntonelliBFSDE.Backward
