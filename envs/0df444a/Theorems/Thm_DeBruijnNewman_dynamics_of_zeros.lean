-- Prove2me | Theorems.Thm_DeBruijnNewman_dynamics_of_zeros
-- name    : DeBruijnNewman.dynamics_of_zeros
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:30:14.457223+00:00
-- url     : https://prove2.me/theorems/c76aa5a5-7094-49ae-af1f-ac0ca844b7e7
-- title:
--   Theorem 11 - the zeros evolve by the repulsive gradient flow
-- statement:
--   Theorem 11. Let $x$ assign to each time $t$ with $\Lambda < t \le 0$ an enumeration $(x_j(t))_{j \in \mathbb{Z}^*}$ of the zeros of $H_t$. Then for each nonzero index $k$ the function $t \mapsto x_k(t)$ is continuously differentiable on $(\Lambda, 0]$ and satisfies the equation of motion
--   $$\partial_t x_k(t) = 2 \sum_{j \ne k}' \frac{1}{x_k(t) - x_j(t)},$$
--   equation (56), where the primed sum is a principal value: the symmetric partial sums over $0 < |j| \le J$, $j \ne k$, converge as $J \to \infty$, and twice their limit is the derivative. Differentiability and continuity of the derivative are taken relative to the interval $(\Lambda, 0]$, since the family is only given there. The hypothesis is satisfiable only when $\Lambda < 0$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Theorem 11, equation (56), p. 27

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros

namespace DeBruijnNewman

theorem dynamics_of_zeros (x : ℝ → ℤ → ℝ)
    (hx : ∀ t : ℝ, Lambda < t → t ≤ 0 → IsZeroEnumeration t (x t)) :
    (∀ k : ℤ, k ≠ 0 →
      ContinuousOn (fun s : ℝ => derivWithin (fun r : ℝ => x r k) (Set.Ioc Lambda 0) s)
        (Set.Ioc Lambda 0)) ∧
    ∀ k : ℤ, k ≠ 0 → ∀ t : ℝ, Lambda < t → t ≤ 0 →
      ∃ S : ℝ,
        Filter.Tendsto
          (fun J : ℕ => ∑ j ∈ ((Finset.Icc (-(J : ℤ)) (J : ℤ)).erase 0).erase k,
            1 / (x t k - x t j)) Filter.atTop (nhds S) ∧
        HasDerivWithinAt (fun s : ℝ => x s k) (2 * S) (Set.Ioc Lambda 0) t := by sorry

end DeBruijnNewman
