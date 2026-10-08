-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Potential_psi_rewrite_lower_bound
-- name    : AdaptiveStepIPM.Potential.psi_rewrite_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:45:27.139282+00:00
-- url     : https://prove2.me/theorems/4890716f-6e25-4f66-aa21-cab61d2834f4
-- title:
--   §5 — $\psi = (\rho-n)\log(x^Ts) - \sum_j \log\frac{x_js_j}{x^Ts/n} + n\log n \ge (\rho-n)\log(x^Ts) + n\log n$
-- statement:
--   Let $n \ge 1$, $\rho \in \mathbb R$, and $x, s \in \mathbb R^n$ with $x > 0$, $s > 0$. Let $\psi(x,s) = \rho\log(x^Ts) - \sum_{j=1}^n\log(x_js_j)$ be the primal–dual potential (1). Then:
--   1. the potential can be rewritten as
--   $$
--   \psi(x,s) = (\rho - n)\log(x^Ts) - \sum_{j=1}^n \log\Bigl(\frac{x_j s_j}{x^Ts/n}\Bigr) + n\log n ;
--   $$
--   2. the sum $\sum_{j}\log\bigl(x_js_j/(x^Ts/n)\bigr)$ is nonpositive (arithmetic–geometric mean inequality), so
--   $$
--   \psi(x,s) \ge (\rho - n)\log(x^Ts) + n\log n ;
--   $$
--   3. consequently, if $\rho > n$, $t \ge 0$ and $\psi(x,s) \le -(\rho-n)t + n\log n$, then $x^Ts \le 2^{-t}$.
--
--   The lower bound turns a decrease of the potential into a decrease of the duality gap: once $\psi$ has been driven down to $-(\rho-n)t + n\log n$, precision $t$ has been reached.
--
--   **Formalization Note** $\psi$ is the published `LinearOptimization.interiorPointPotential ρ x s`, which agrees with (1) for $x, s > 0$. All logarithms are natural; the third item uses $e^{-t} \le 2^{-t}$ for $t \ge 0$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 11, §5 (displays before Algorithm 3)

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood

open Matrix

namespace AdaptiveStepIPM.Potential

/-- **§5, p. 11.** For `x, s > 0` the potential (1) can be written as
`ψ(x, s) = (ρ − n) log(xᵀs) − Σⱼ log(x_j s_j/(xᵀs/n)) + n log n`; the sum is nonpositive
(arithmetic–geometric mean inequality), so `ψ(x, s) ≥ (ρ − n) log(xᵀs) + n log n`; hence,
for `ρ > n` and `t ≥ 0`, `ψ(x, s) ≤ −(ρ − n)t + n log n` implies `xᵀs ≤ 2^{−t}`. -/
theorem psi_rewrite_lower_bound {n : ℕ} (hn : 1 ≤ n) (ρ : ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    LinearOptimization.interiorPointPotential ρ x s =
        (ρ - n) * Real.log (x ⬝ᵥ s) -
          ∑ j, Real.log (x j * s j / ((x ⬝ᵥ s) / n)) + n * Real.log n ∧
      (ρ - n) * Real.log (x ⬝ᵥ s) + n * Real.log n ≤
        LinearOptimization.interiorPointPotential ρ x s ∧
      ∀ t : ℝ, (n : ℝ) < ρ → 0 ≤ t →
        LinearOptimization.interiorPointPotential ρ x s ≤ -((ρ - n) * t) + n * Real.log n →
        x ⬝ᵥ s ≤ (2 : ℝ) ^ (-t) := by sorry

end AdaptiveStepIPM.Potential
