-- Prove2me | Theorems.Thm_Devaney_quadratic_ncard_perOfPeriod
-- name    : Devaney.quadratic_ncard_perOfPeriod
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T11:12:24.9667+00:00
-- url     : https://prove2.me/theorems/0eb08e60-1538-491e-935f-11a4b7aa2a4c
-- title:
--   Theorem 7.5(1) — $F_\mu$ has exactly $2^n$ points of period $n$
-- statement:
--   Let $\mu > 2 + \sqrt 5$ and $n \ge 1$. The set of points of $\Lambda$ fixed by $F_\mu^{\,n}$,
--
--   $$\operatorname{Per}_n(F_\mu) = \{x \in \Lambda : F_\mu^{\,n}(x) = x\},$$
--
--   has exactly $2^{n}$ elements.
--
--   Computing these $2^n$ roots of a degree-$2^n$ polynomial directly is hopeless; the conjugacy with the shift delivers the count for free.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, p. 47, Theorem 7.5(1)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem quadratic_ncard_perOfPeriod (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) (n : ℕ) (hn : 0 < n) :
    (PerOfPeriod (Lambda μ) (quadratic μ) n).ncard = 2 ^ n := by sorry
end Devaney
