-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p43_sales_per_unit_decreasing
-- name    : CachonCoord.EffortNewsvendor.p43_sales_per_unit_decreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:56.871186+00:00
-- url     : https://prove2.me/theorems/96dcd05b-2b25-4148-8eb8-92ba0dd7f6f7
-- title:
--   §6.4.1, p. 43 — expected sales per unit ordered, S(q, e)/q, is decreasing in q
-- statement:
--   In the effort model of §6.4.1, fix an effort level $e \ge 0$. Expected sales per unit ordered,
--
--   $$
--   q \longmapsto \frac{S(q, e)}{q}, \qquad q > 0,
--   $$
--
--   is strictly decreasing.
--
--   The book invokes this fact at $e = e^o$ to call $w_d$ a quantity discount schedule: the revenue part $(1 - \lambda)pS(q, e^o)/q$ of the per-unit price falls as the order grows.
--
--   **Formalization Note** The statement is the strict version. It holds because $F(\cdot \mid e)$ is strictly increasing on $[0, \infty)$ with $F(0 \mid e) = 0$, a standing assumption of the chapter (p. 7).
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, p. 43, "Given that S(q, e°)/q is decreasing in q"

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- p. 43, "Given that S(q, e°)/q is decreasing in q": for every effort level `e ≥ 0`, expected
sales per unit ordered `q ↦ S(q, e)/q` is strictly decreasing on `q > 0`. -/
theorem p43_sales_per_unit_decreasing (M : Model) (e : ℝ) (he : 0 ≤ e) :
    StrictAntiOn (fun q => M.S q e / q) (Set.Ioi 0) := by sorry

end CachonCoord.EffortNewsvendor
