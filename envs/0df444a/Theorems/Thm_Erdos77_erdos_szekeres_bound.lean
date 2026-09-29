-- Prove2me | Theorems.Thm_Erdos77_erdos_szekeres_bound
-- name    : Erdos77.erdos_szekeres_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T18:30:00.913663+00:00
-- url     : https://prove2.me/theorems/c7de81e4-1564-4cb8-abcb-58d940f33674
-- title:
--   Erdős–Szekeres 1935: $R(k) \le \binom{2k-2}{k-1}$
-- statement:
--   For every integer $k\ge1$,
--
--   $$
--   R(k)\ \le\ \binom{2k-2}{k-1}.
--   $$
--
--   This is the diagonal case of the Erdős–Szekeres bound $R(k,\ell)\le\binom{k+\ell-2}{k-1}$. In particular $R(k)$ is finite (Ramsey's theorem for two colours), $R(k)<4^{k}$, and $\limsup_k R(k)^{1/k}\le 4$.
-- source:
--   P. Erdős and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935), 463–470, http://www.numdam.org/item/CM_1935__2__463_0/ (bound R(k,l) ≤ C(k+l−2, k−1), diagonal case k = l).

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem erdos_szekeres_bound (k : ℕ) (hk : 1 ≤ k) :
    diagonalRamsey k ≤ Nat.choose (2 * k - 2) (k - 1) := by sorry
end Erdos77
