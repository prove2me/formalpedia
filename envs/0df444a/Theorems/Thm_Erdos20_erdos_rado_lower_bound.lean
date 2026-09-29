-- Prove2me | Theorems.Thm_Erdos20_erdos_rado_lower_bound
-- name    : Erdos20.erdos_rado_lower_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T17:27:57.782502+00:00
-- url     : https://prove2.me/theorems/93c38790-d4b6-4c83-a848-ac18e5dfce3f
-- title:
--   Erdős–Rado lower bound $(k-1)^n < f(n,k)$
-- statement:
--   Let $f(n,k)$ be the sunflower threshold. For all integers $n \ge 1$ and $k \ge 2$,
--
--   $$(k-1)^n < f(n,k).$$
--
--   Equivalently, there is a family of $(k-1)^n$ sets of size $n$ with no $k$-sunflower. Together with the upper bound this shows that an exponential bound $c_k^{\,n}$ would be the correct order of growth.
-- source:
--   P. Erdős and R. Rado, Intersection theorems for systems of sets, J. London Math. Soc. 35 (1960), 85–90, https://doi.org/10.1112/jlms/s1-35.1.85 ; the bound $(p-1)^k < \mathrm{Sun}(p,k)$ as quoted in Bell–Chueluecha–Warnke, Note on sunflowers, arXiv:2009.09327, Introduction, p. 1

import Definitions.Def_Erdos20_defs
import Mathlib

namespace Erdos20
theorem erdos_rado_lower_bound :
    ∀ n k, n > 0 → 2 ≤ k → (k - 1) ^ n < f n k := by sorry
end Erdos20
