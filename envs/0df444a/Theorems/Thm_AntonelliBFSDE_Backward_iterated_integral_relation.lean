-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_iterated_integral_relation
-- name    : AntonelliBFSDE.Backward.iterated_integral_relation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:01.823732+00:00
-- url     : https://prove2.me/theorems/7343a440-246d-4006-ae6d-ac4620f4f2b0
-- title:
--   Proof of Theorem 2.4, p. 780 — $\sum_{i=0}^n(-1)^iA_t^{((n-i)-)}A_t^{(i)}=0$
-- statement:
--   Let $a:[0,\infty)\to\mathbb R$ be nondecreasing and right-continuous with $a_0=0$, and let $a^{(n)}$, $a^{(n-)}$ be its iterated Lebesgue–Stieltjes integrals (without and with left limits of the integrand). Then for every $n\ge1$ and every $t\ge0$,
--   $$\sum_{i=0}^n(-1)^i\,a_t^{((n-i)-)}\,a_t^{(i)}=0 .$$
--   For $n=2$ this is the integration by parts formula $a_t^2=(a\cdot a)_t+(a_-\cdot a)_t$.
--
--   In the proof of Theorem 2.4 this identity is applied pathwise to the nondecreasing integrator $A$ (after the reduction "without loss of generality $A$ is increasing"); it is what makes the brackets $(A_u-A_t)^{[n]}$ vanish at $u=t$.
--
--   **Formalization Note** The paper writes the relation "for all $t\in[0,T]$" with $n$ implicit; for $n=0$ the sum equals $1$, so the statement is for $n\ge1$. It is stated for a deterministic path, which is how it is used.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 780, proof of Theorem 2.4 (notation paragraph)

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Proof of Theorem 2.4, p. 780: for a nondecreasing right-continuous path `a` with `a(0) = 0`,
the iterated integrals `a^{(n)}` and `a^{(n-)}` satisfy
`∑_{i=0}^n (-1)^i a_t^{((n-i)-)} a_t^{(i)} = 0` for every `n ≥ 1` and every `t`. -/
theorem iterated_integral_relation (a : ℝ≥0 → ℝ) (ha_mono : Monotone a)
    (ha_rc : ∀ t, ContinuousWithinAt a (Set.Ici t) t) (ha_zero : a 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * iterIntMinus a (n - i) t * iterInt a i t = 0 := by sorry

end AntonelliBFSDE.Backward
