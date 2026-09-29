-- Prove2me | Theorems.Thm_Devaney_shift_dense_per
-- name    : Devaney.shift_dense_per
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:43:08.729028+00:00
-- url     : https://prove2.me/theorems/d127b9e9-1c8a-4dc6-bc49-0f9f26299424
-- title:
--   Proposition 6.6(2) — periodic points of $\sigma$ are dense
-- statement:
--   The set of periodic points of the shift,
--
--   $$\operatorname{Per}(\sigma) = \{ s \in \Sigma_2 : \sigma^{n}(s) = s \text{ for some } n > 0 \},$$
--
--   is dense in $\Sigma_2$: every sequence is a limit of repeating sequences. Indeed, truncating $s$ after its $n$-th entry and repeating the block gives a periodic sequence within $2^{-n}$ of $s$.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.6, p. 42, Proposition 6.6(2)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem shift_dense_per : Dense (Per (Set.univ : Set Sigma2) shift) := by sorry
end Devaney
