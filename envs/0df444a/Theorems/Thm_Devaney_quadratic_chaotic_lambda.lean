-- Prove2me | Theorems.Thm_Devaney_quadratic_chaotic_lambda
-- name    : Devaney.quadratic_chaotic_lambda
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:15:23.443241+00:00
-- url     : https://prove2.me/theorems/b21d671c-3b43-4066-bae3-06e5abf86f7a
-- title:
--   Example 8.8 (goal) — $F_\mu$ is chaotic on $\Lambda$ for $\mu > 2+\sqrt5$
-- statement:
--   **Goal of the mission.** For every $\mu > 2 + \sqrt 5$, the quadratic map $F_\mu(x) = \mu x(1-x)$ is chaotic, in Devaney's sense, on its invariant Cantor set
--
--   $$\Lambda = \{x : F_\mu^{\,n}(x) \in [0,1] \text{ for all } n \ge 0\} .$$
--
--   That is: $F_\mu$ has sensitive dependence on initial conditions on $\Lambda$, it is topologically transitive on $\Lambda$, and its periodic points are dense in $\Lambda$.
--
--   This is the book's flagship example of a chaotic system, and the prototype for every later "chaos via symbolic dynamics" argument in the text: the chaos is established not by direct analysis of $F_\mu$, whose invariant set has no closed-form description, but by transporting the corresponding properties of the shift map along the itinerary conjugacy.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.8, p. 50, Example 8.8 (Definition 8.5, p. 50)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_chaotic_lambda (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    Chaotic (Lambda μ) (quadratic μ) := by sorry
end Devaney
