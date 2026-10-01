-- Prove2me | Theorems.Thm_BealeConvexMin_RandomLP_discrete_expected_cost_lp
-- name    : BealeConvexMin.RandomLP.discrete_expected_cost_lp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:43:14.199837+00:00
-- url     : https://prove2.me/theorems/3512ed2e-ad71-40b4-a294-43711649f48e
-- title:
--   Beale (1955), eqs. (5.5)–(5.6): with a discrete distribution, E(C) is the value of a linear program
-- statement:
--   Suppose the data are discrete: there are finitely many scenarios $r$, and with probability $p_r$ the data take the values $A=A_r$, $\beta=\beta_r$. Fix a non-negative first-stage vector $x\in\mathbb R^n$ and assume that in every scenario the second-stage minimum $\min\{f'y: y\ge0,\ A_rx+Dy=\beta_r\}$ is attained. Then the mean cost $E(C)(x)$ is the least value of
--   $$c'x+\sum_r p_r\,f'y_r\tag{5.5}$$
--   over all families of non-negative vectors $y_r$ satisfying
--   $$A_rx+Dy_r=\beta_r\quad\text{for all } r.\tag{5.6}$$
--
--   Consequently, minimising $E(C)$ over non-negative $x$ is the linear program of choosing non-negative $x$ and $y_r$ to minimise (5.5) subject to (5.6): the precise sense in which Beale's problem "can also be regarded as a special case of linear programming if the random variables have discrete distributions".
--
--   **Formalization Note** The scenarios form a finite type $R$ with a probability measure $P$ on it (all subsets measurable), $p_r=P(\{r\})$, and the data are functions $A:R\to\mathbb R^{m\times n}$, $\beta:R\to\mathbb R^m$. Scenarios of probability zero are allowed; the attainment hypothesis is imposed on every scenario, so that the constraint (5.6) is satisfiable in each.
-- source:
--   Beale, On Minimizing a Convex Function Subject to Linear Inequalities, J. R. Statist. Soc. B 17(2), 1955, https://doi.org/10.1111/j.2517-6161.1955.tb00191.x, p. 182 (PDF p. 10), eqs. (5.5)–(5.6)

import Mathlib
import Definitions.Def_BealeConvexMin_RandomLP_secondStageValue
import Definitions.Def_BealeConvexMin_RandomLP_expectedCost

namespace BealeConvexMin.RandomLP

open Matrix MeasureTheory

/-- Beale (1955), §5, p. 182, eqs. (5.5)–(5.6): for a discrete distribution, with probability
`p_r = P {r}` that `A = A_r` and `β = β_r` over a finite set of scenarios `r`, the mean cost `E(C)`
at `x` is the least value of `c′x + Σ_r p_r f′y_r` (eq. (5.5)) over non-negative `y_r` satisfying
`A_r x + D y_r = β_r` for all `r` (eq. (5.6)); so minimising `E(C)` is a linear program. The
second-stage minimum is assumed attained in every scenario. -/
theorem discrete_expected_cost_lp {R : Type*} [Fintype R] [MeasurableSpace R]
    [MeasurableSingletonClass R] (P : Measure R) [IsProbabilityMeasure P] {m n p : ℕ}
    (c : Fin n → ℝ) (f : Fin p → ℝ) (D : Matrix (Fin m) (Fin p) ℝ)
    (A : R → Matrix (Fin m) (Fin n) ℝ) (β : R → Fin m → ℝ) (x : Fin n → ℝ) (hx : 0 ≤ x)
    (hatt : ∀ r, SecondStageAttained D f (β r - A r *ᵥ x)) :
    IsLeast {z : ℝ | ∃ y : R → Fin p → ℝ,
        (∀ r, 0 ≤ y r ∧ A r *ᵥ x + D *ᵥ y r = β r) ∧
          z = c ⬝ᵥ x + ∑ r, (P {r}).toReal * (f ⬝ᵥ y r)}
      (expectedCost P c f D A β x) := by sorry

end BealeConvexMin.RandomLP
