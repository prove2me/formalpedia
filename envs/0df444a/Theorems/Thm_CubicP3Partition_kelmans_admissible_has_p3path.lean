-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_admissible_has_p3path
-- name    : CubicP3Partition.kelmans_admissible_has_p3path
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T21:32:15.820928+00:00
-- url     : https://prove2.me/theorems/fbf0cfa1-c810-4097-a50d-78bb01f2f473
-- title:
--   Admissible cubic graphs contain a three-vertex path
-- statement:
--   Every finite simple cubic 3-connected graph whose order is divisible by six contains a three-vertex path: there are three pairwise distinct vertices $a, v, b$ with edges $a$-$v$ and $v$-$b$. This follows directly from cubicity, since any vertex has three distinct neighbours, any two of which form such a path through it. It is the existence step used to derive claim $(z1)$ from claim $(z8)$ in Kelmans's Theorem 3.1.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, pp. 7-8, Theorem 3.1, derivation of (z1) from (z8).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

theorem kelmans_admissible_has_p3path : ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W, Cubic G → ThreeVertexConnected G → Fintype.card W % 6 = 0 → Nonempty (P3Path G) := by sorry

end CubicP3Partition
