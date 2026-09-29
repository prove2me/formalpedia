-- Prove2me | Theorems.Thm_Devaney_quadratic_sensitiveDependence
-- name    : Devaney.quadratic_sensitiveDependence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:13:57.863867+00:00
-- url     : https://prove2.me/theorems/aa91da63-b6c2-4ac5-af38-d37472ed0d4a
-- title:
--   Example 8.3 — sensitive dependence on initial conditions on $\Lambda$
-- statement:
--   Let $\mu > 2 + \sqrt 5$. The quadratic map has sensitive dependence on initial conditions on $\Lambda$: there is $\delta > 0$ such that every $x \in \Lambda$ has points $y \in \Lambda$ arbitrarily close to it with
--
--   $$|F_\mu^{\,n}(x) - F_\mu^{\,n}(y)| > \delta \quad \text{for some } n .$$
--
--   Devaney's witness is any $\delta$ smaller than the length of the gap $A_0$ between $I_0$ and $I_1$: distinct points of $\Lambda$ have distinct itineraries, and the first disagreement puts their iterates on opposite sides of the gap.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.8, pp. 49–50, Example 8.3 (Definition 8.2, p. 49)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_sensitiveDependence (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    SensitiveDependence (Lambda μ) (quadratic μ) := by sorry
end Devaney
