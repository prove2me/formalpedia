-- Prove2me | Theorems.Thm_Devaney_quadratic_tendsto_atBot_of_notMem_unitI
-- name    : Devaney.quadratic_tendsto_atBot_of_notMem_unitI
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:11:08.81118+00:00
-- url     : https://prove2.me/theorems/d4dfdee3-4df8-400f-887b-678532a651d3
-- title:
--   Proposition 5.2 — orbits outside $[0,1]$ tend to $-\infty$
-- statement:
--   Let $F_\mu(x) = \mu x(1-x)$ with $\mu > 1$.
--
--   If the initial point lies outside the unit interval — either $x < 0$ or $x > 1$ — then its orbit diverges to $-\infty$:
--
--   $$F_\mu^{\,n}(x) \longrightarrow -\infty \qquad (n \to \infty).$$
--
--   This is the statement that all the interesting dynamics of the quadratic family happens inside $I = [0,1]$: outside $I$ the behaviour is completely tame.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.5, p. 32, Proposition 5.2

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_tendsto_atBot_of_notMem_unitI (μ x : ℝ) (hμ : 1 < μ)
    (hx : x < 0 ∨ 1 < x) :
    Filter.Tendsto (fun n : ℕ => (quadratic μ)^[n] x) Filter.atTop Filter.atBot := by sorry
end Devaney
