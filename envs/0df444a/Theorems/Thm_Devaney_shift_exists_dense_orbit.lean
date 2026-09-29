-- Prove2me | Theorems.Thm_Devaney_shift_exists_dense_orbit
-- name    : Devaney.shift_exists_dense_orbit
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:47:45.724183+00:00
-- url     : https://prove2.me/theorems/f7fbc7f5-d173-433c-952d-da32fe9c162e
-- title:
--   Proposition 6.6(3) — $\sigma$ has a dense orbit
-- statement:
--   There is a sequence $s^\ast \in \Sigma_2$ whose forward orbit under the shift is dense: the closure of $\{\sigma^{n}(s^\ast) : n \ge 0\}$ is all of $\Sigma_2$.
--
--   Devaney's witness is the sequence obtained by listing, in order, all binary blocks of length $1$, then all blocks of length $2$, then length $3$, and so on; some iterate of $\sigma$ then makes $s^\ast$ agree with any prescribed sequence on an arbitrarily long initial block.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, p. 42, Proposition 6.6(3)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem shift_exists_dense_orbit :
    ∃ s : Sigma2, Dense {t : Sigma2 | ∃ n : ℕ, shift^[n] s = t} := by sorry
end Devaney
