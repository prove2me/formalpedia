-- Prove2me | Theorems.Thm_CachonCoord_EffortNewsvendor_p41_expected_sales
-- name    : CachonCoord.EffortNewsvendor.p41_expected_sales
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:45.799807+00:00
-- url     : https://prove2.me/theorems/2a0e6b4f-1f7e-4113-8d26-3e69fafe3558
-- title:
--   §6.4.1, p. 41 — expected sales given effort: S(q, e) = q − ∫₀^q F(y|e) dy
-- statement:
--   In the effort model of §6.4.1, let $D$ have the demand law given effort $e \ge 0$, with distribution function $F(\cdot \mid e)$ on $[0, \infty)$. For every order quantity $q \ge 0$, expected sales $S(q, e) = \mathbb E[\min(q, D)]$ satisfy
--
--   $$
--   S(q, e) = q - \int_0^q F(y \mid e)\,dy.
--   $$
--
--   This is the form of expected sales in which the section differentiates with respect to effort.
--
--   **Formalization Note** The book writes this display as the definition of $S$. The formalization defines $S$ as the expectation and states the integral form as a theorem.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.4.1, p. 41, the display of S(q, e)

import Mathlib
import Definitions.Def_CachonCoord_EffortNewsvendor_Model

namespace CachonCoord.EffortNewsvendor

/-- p. 41, the display after `Π(q, e)`: expected sales given effort `e` satisfy
`S(q, e) = q − ∫_0^q F(y|e) dy` for `q ≥ 0` and every effort level `e ≥ 0`. -/
theorem p41_expected_sales (M : Model) (q e : ℝ) (hq : 0 ≤ q) (he : 0 ≤ e) :
    M.S q e = q - ∫ y in (0 : ℝ)..q, M.F y e := by sorry

end CachonCoord.EffortNewsvendor
