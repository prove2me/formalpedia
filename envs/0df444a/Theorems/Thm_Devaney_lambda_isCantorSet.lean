-- Prove2me | Theorems.Thm_Devaney_lambda_isCantorSet
-- name    : Devaney.lambda_isCantorSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:27:17.682706+00:00
-- url     : https://prove2.me/theorems/66e94f8e-56e3-4821-95fa-567cd29f708b
-- title:
--   Theorem 5.6 — $\Lambda$ is a Cantor set
-- statement:
--   Let $\mu > 2 + \sqrt 5$ and let
--
--   $$\Lambda = \{x : F_\mu^{\,n}(x) \in [0,1] \text{ for all } n \ge 0\}$$
--
--   be the set of points whose forward orbit never leaves the unit interval. Then $\Lambda$ is a **Cantor set**: it is a closed subset of $[0,1]$, it contains no nondegenerate interval, and every one of its points is an accumulation point of $\Lambda$.
--
--   The hypothesis $\mu > 2+\sqrt5$ is exactly what makes $|F_\mu'| > 1$ hold on $I_0 \cup I_1$, which drives the total disconnectedness. Devaney remarks that the conclusion is still true for all $\mu > 4$, but by a more delicate argument.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.5, pp. 37–38, Theorem 5.6 (Cantor set: Definition 5.4, p. 37)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem lambda_isCantorSet (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) : IsCantorSet (Lambda μ) := by sorry
end Devaney
