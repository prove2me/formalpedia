-- Prove2me | Theorems.Thm_AffineVolterra_Existence_theorem_3_6
-- name    : AffineVolterra.Existence.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:58.664985+00:00
-- url     : https://prove2.me/theorems/a5b80bd9-e048-48c5-91d6-9f1f17854cee
-- title:
--   Theorem 3.6 — nonnegative continuous weak solution
-- statement:
--   Let $K$ be diagonal with scalar entries $K_i$ that satisfy condition (2.5), each with its own admissible exponent, and condition (3.4): $K_i$ is nonnegative, nonzero, nonincreasing and continuous on $(0,\infty)$, and has a nonnegative first-kind resolvent $L_i$ whose interval masses $s\mapsto L_i([s,s+t])$ are nonincreasing for every $t\ge0$. Suppose $b$ and $\sigma$ are continuous, satisfy (3.1), and obey, for every $x\in\mathbb R^d$ and every coordinate $i$,
--
--   $$
--   x_i=0\quad\Longrightarrow\quad b_i(x)\ge0\quad\text{and}\quad \sigma_{ik}(x)=0\ \text{for every }k.
--   $$
--
--   Then, for every $x_0\in\mathbb R^d_+$, equation (1.1) has a continuous weak solution with values in $\mathbb R^d_+$ at every fixed time almost surely.
--
--   The theorem gives stochastic invariance of the nonnegative orthant for these non-Markovian convolution equations.
--
--   **Formalization Note** The boundary condition is imposed on all of $\mathbb R^d$ as printed, not just on nonnegative states. Weak existence chooses the probability space and Brownian motion; the Itô convolution is constrained by the published Brownian integral relation. Continuity of paths turns fixed-time almost-sure orthant membership into an indistinguishable orthant-valued version.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Theorem 3.6 and (3.4), p. 14

import Mathlib
import Definitions.Def_AffineVolterra_Existence_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace AffineVolterra.Existence

/-- Theorem 3.6, p. 14: existence of an orthant-valued continuous weak solution. -/
theorem theorem_3_6 {d m : ℕ} (K : Kernel d)
    (Kd : Fin d → ℝ → ℝ) (b : State d → State d) (σ : Diffusion d m)
    (hdiag : IsDiagKernel K Kd)
    (hL2 : ∀ i j, LpLoc 2 (fun t => K t i j))
    (h25 : ∀ i, ∃ γ : ℝ, Cond25 (Kd i) γ)
    (h34 : ∀ i, Cond34 (Kd i))
    (hb : Continuous b) (hσ : Continuous σ)
    (cLG : ℝ) (hgrowth : LinGrowth b σ cLG)
    (hboundary : ∀ x : State d, ∀ i : Fin d,
      x i = 0 → 0 ≤ b x i ∧ ∀ k : Fin m, σ x i k = 0) :
    ∀ x₀ : State d, x₀ ∈ NonnegativeOrthant d →
      HasWeakSolution K b σ x₀ (NonnegativeOrthant d) := by sorry

end AffineVolterra.Existence
