-- Prove2me | Theorems.Thm_CachonCoord_Proportional_p52_what_induces
-- name    : CachonCoord.Proportional.p52_what_induces
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:44:37.359482+00:00
-- url     : https://prove2.me/theorems/da5cda44-2ae5-43f0-a482-b03cd133ee8e
-- title:
--   pp. 51–52 — the wholesale price ŵ(q) induces the retailers to order q in total (unique equilibrium q/n each)
-- statement:
--   Let $n \ge 2$ and $q > 0$, and let
--
--   $$
--   \widehat w(q) = p\left(1 - \left(\frac1n\right)F(q) - \left(\frac{n-1}{n}\right)\left(\frac1q\int_0^q F(x)\,dx\right)\right).
--   $$
--
--   Under the wholesale-price contract with $w = \widehat w(q)$ and $b = 0$, a profile of orders is a Nash equilibrium if and only if every retailer orders $q/n$.
--
--   So $\widehat w(q)$ is the wholesale price that induces total stock $q$, and $\widehat w(q^o)$ is the coordinating wholesale price.
--
--   **Formalization Note** $\widehat w$ is the printed formula; that it induces $q$ is the content of this theorem. The hypotheses on the demand law are the chapter's standing assumptions (p. 7), carried by the model.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.5.1, pp. 51–52 (definition and display of ŵ(q))

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand
import Definitions.Def_CachonCoord_Proportional_Nash
import Definitions.Def_CachonCoord_Proportional_Game

namespace CachonCoord.Proportional

/-- p. 51–52: `ŵ(q)` is "the wholesale price that induces the retailers to order `q` units with a
wholesale price contract (i.e., with `b = 0`). From (22),
`ŵ(q) = p (1 − (1/n) F(q) − ((n − 1)/n) (1/q) ∫_0^q F(x) dx)`." For every `q > 0`, under the
wholesale price contract `w = ŵ(q)`, `b = 0`, a profile is a Nash equilibrium if and only if every
retailer orders `q/n`. -/
theorem p52_what_induces (M : Model) (n : ℕ) (hn : 2 ≤ n) (q : ℝ) (hq : 0 < q) :
    ∀ r : Fin n → ℝ, M.IsNashEq (M.what n q) 0 r ↔ ∀ i, r i = q / n := by sorry

end CachonCoord.Proportional
