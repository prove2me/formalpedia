-- Prove2me | Theorems.Thm_Devaney_shift_ncard_perOfPeriod
-- name    : Devaney.shift_ncard_perOfPeriod
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:41:42.605239+00:00
-- url     : https://prove2.me/theorems/bbb8b55f-eb5b-4eca-9c90-180438c30955
-- title:
--   Proposition 6.6(1) — $\sigma$ has exactly $2^n$ points of period $n$
-- statement:
--   For every $n \ge 1$, the set of sequences fixed by the $n$-th iterate of the shift,
--
--   $$\operatorname{Per}_n(\sigma) = \{ s \in \Sigma_2 : \sigma^{n}(s) = s \},$$
--
--   has exactly $2^{n}$ elements: the points of period $n$ are precisely the repeating sequences $(s_0 \dots s_{n-1}\, s_0 \dots s_{n-1} \dots)$, one for each of the $2^n$ binary words of length $n$.
--
--   The restriction $n \ge 1$ is necessary: $\sigma^0$ is the identity, so every sequence would be "fixed" and the count would be infinite.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, p. 42, Proposition 6.6(1)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem shift_ncard_perOfPeriod (n : ℕ) (hn : 0 < n) :
    (PerOfPeriod (Set.univ : Set Sigma2) shift n).ncard = 2 ^ n := by sorry
end Devaney
