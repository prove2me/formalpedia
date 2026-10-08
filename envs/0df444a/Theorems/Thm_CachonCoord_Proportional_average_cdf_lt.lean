-- Prove2me | Theorems.Thm_CachonCoord_Proportional_average_cdf_lt
-- name    : CachonCoord.Proportional.average_cdf_lt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:31:18.655134+00:00
-- url     : https://prove2.me/theorems/247bdabc-9d10-44ab-9d28-a99d6b39f0c6
-- title:
--   p. 52 — (1/q)∫₀^q F(x)dx < F(q) for q > 0
-- statement:
--   Let $F$ be the distribution function of total demand, continuous and strictly increasing on $[0,\infty)$ with $F(0) = 0$. For every $q > 0$,
--
--   $$
--   \frac1q\int_0^q F(x)\,dx < F(q).
--   $$
--
--   The average of $F$ over $[0,q]$ is strictly below its value at the right end. The inequality drives the uniqueness of the equilibrium in (21)–(22) and the comparison $\widehat w(q^o) > c$.
--
--   **Formalization Note** $q > 0$ is required: at $q = 0$ both sides are $0$. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, p. 52 (the display 1/q ∫_0^q F(x)dx < F(q))

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand

namespace CachonCoord.Proportional

/-- p. 52: for every `q > 0`, `(1/q) ∫_0^q F(x) dx < F(q)`. -/
theorem average_cdf_lt (M : Model) (q : ℝ) (hq : 0 < q) : M.avgF q < M.F q := by sorry

end CachonCoord.Proportional
