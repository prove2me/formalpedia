-- Prove2me | Theorems.Thm_Devaney_lambdaMap_conjugate_shift
-- name    : Devaney.lambdaMap_conjugate_shift
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:54:12.28776+00:00
-- url     : https://prove2.me/theorems/d3a64917-52b3-4503-b126-690550c6f793
-- title:
--   Corollary of Theorems 7.2–7.3 — $F_\mu|_\Lambda$ is conjugate to the shift
-- statement:
--   Let $\mu > 2 + \sqrt 5$. The restriction of $F_\mu$ to its invariant Cantor set $\Lambda$ is topologically conjugate to the shift map on $\Sigma_2$: there is a homeomorphism $h : \Lambda \to \Sigma_2$ with
--
--   $$h \circ F_\mu|_\Lambda = \sigma \circ h .$$
--
--   This is the statement the book uses when it says the shift is "an exact model" for the quadratic map: all dynamical features — fixed points, periodic orbits of each period, dense orbits, transitivity — transfer between the two systems.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, p. 47, Definition 7.4 and the paragraph following it (consequence of Theorems 7.2 and 7.3)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem lambdaMap_conjugate_shift (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    TopologicallyConjugate (lambdaMap μ) shift := by sorry
end Devaney
