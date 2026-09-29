-- Prove2me | Theorems.Thm_Devaney_quadratic_exists_dense_orbit
-- name    : Devaney.quadratic_exists_dense_orbit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:13:33.301184+00:00
-- url     : https://prove2.me/theorems/25c0a143-1eb1-49ec-920c-248ba10501c0
-- title:
--   Theorem 7.5(3) — $F_\mu$ has a dense orbit in $\Lambda$
-- statement:
--   Let $\mu > 2 + \sqrt 5$. There is a point $x \in \Lambda$ whose forward orbit is dense in $\Lambda$:
--
--   $$\Lambda \subseteq \overline{\{F_\mu^{\,n}(x) : n \ge 0\}} .$$
--
--   Equivalently, some single orbit of the quadratic map winds densely through the whole Cantor set — the image under the conjugacy of Devaney's explicit dense orbit for the shift.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, p. 47, Theorem 7.5(3)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_exists_dense_orbit (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    ∃ x ∈ Lambda μ, Lambda μ ⊆ closure {y : ℝ | ∃ n : ℕ, (quadratic μ)^[n] x = y} := by sorry
end Devaney
