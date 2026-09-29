-- Prove2me | Theorems.Thm_Devaney_quadratic_dense_per
-- name    : Devaney.quadratic_dense_per
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:12:58.625714+00:00
-- url     : https://prove2.me/theorems/904ed3ee-9f74-40d3-81dc-af69ad26baf9
-- title:
--   Theorem 7.5(2) — periodic points are dense in $\Lambda$
-- statement:
--   Let $\mu > 2 + \sqrt 5$. The periodic points of $F_\mu$ lying in $\Lambda$ are dense in $\Lambda$:
--
--   $$\Lambda \subseteq \overline{\operatorname{Per}(F_\mu)} .$$
--
--   This is the "element of regularity" ingredient of Devaney's definition of chaos, transported from the shift by the conjugacy.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, p. 47, Theorem 7.5(2)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_dense_per (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    Lambda μ ⊆ closure (Per (Lambda μ) (quadratic μ)) := by sorry
end Devaney
