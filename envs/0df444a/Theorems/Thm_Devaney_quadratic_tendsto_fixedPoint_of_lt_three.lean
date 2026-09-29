-- Prove2me | Theorems.Thm_Devaney_quadratic_tendsto_fixedPoint_of_lt_three
-- name    : Devaney.quadratic_tendsto_fixedPoint_of_lt_three
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:16:05.461595+00:00
-- url     : https://prove2.me/theorems/edfb6fdd-0dde-41f8-a530-fa1bae639e5a
-- title:
--   Proposition 5.3 — the tame regime $1 < \mu < 3$
-- statement:
--   Let $1 < \mu < 3$ and $p_\mu = (\mu-1)/\mu$.
--
--   1. $0$ and $p_\mu$ are fixed points of $F_\mu$; the fixed point $p_\mu$ is attracting, $|F_\mu'(p_\mu)| < 1$, while $0$ is repelling, $|F_\mu'(0)| > 1$.
--   2. Every point of the open unit interval is asymptotic to $p_\mu$:
--
--   $$\lim_{n \to \infty} F_\mu^{\,n}(x) = p_\mu \qquad \text{for all } 0 < x < 1 .$$
--
--   For parameters in this range the dynamics of $F_\mu$ is therefore completely understood: two fixed points, and every other point of $I$ attracted to $p_\mu$. It is the regime the chaotic behaviour of the mission's goal is contrasted against.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.5, pp. 32–33, Proposition 5.3 (with part 1 from Example 4.10, p. 30)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_tendsto_fixedPoint_of_lt_three (μ : ℝ) (hμ : 1 < μ) (hμ' : μ < 3) :
    quadratic μ 0 = 0 ∧ quadratic μ ((μ - 1) / μ) = (μ - 1) / μ ∧
      |deriv (quadratic μ) ((μ - 1) / μ)| < 1 ∧ 1 < |deriv (quadratic μ) 0| ∧
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Filter.Tendsto (fun n : ℕ => (quadratic μ)^[n] x) Filter.atTop
          (nhds ((μ - 1) / μ)) := by sorry
end Devaney
