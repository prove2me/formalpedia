-- Prove2me | Theorems.Thm_Devaney_quadratic_four_chaotic_unitI
-- name    : Devaney.quadratic_four_chaotic_unitI
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:14:24.210257+00:00
-- url     : https://prove2.me/theorems/5d2de3a7-b1d4-4c02-9650-ad2ac2b89bb4
-- title:
--   Example 8.9 — $F_4$ is chaotic on the whole interval
-- statement:
--   The map $F_4(x) = 4x(1-x)$ is chaotic on all of $I = [0,1]$ — not merely on a Cantor subset.
--
--   Devaney's proof composes two conjugacies: $\theta \mapsto \cos\theta$ conjugates the angle-doubling map $g(\theta) = 2\theta$ of the circle with $q(x) = 2x^2-1$, and $h_2(t) = \tfrac12(1-t)$ conjugates $q$ with $F_4$; the doubling map is chaotic, and chaos is preserved by conjugacy.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.8, pp. 51–52, Example 8.9 (Definition 8.5, p. 50)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_four_chaotic_unitI : Chaotic unitI (quadratic 4) := by sorry
end Devaney
