-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_p3_factor_extend
-- name    : CubicP3Partition.kelmans_p3_factor_extend
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T21:32:26.34001+00:00
-- url     : https://prove2.me/theorems/fc62242f-0d96-457e-9205-ef85bbb3bfd7
-- title:
--   A $P_3$-factor of the remainder extends across the deleted path
-- statement:
--   Let $G$ be a finite simple graph and $L$ a specified three-vertex path in $G$. If the graph obtained by deleting the three vertices of $L$ has a $P_3$-factor, then $G$ itself has a $P_3$-factor: adjoin the deleted path as one further block to the factor of the remainder. The two edges of the adjoined block are exactly the two edges of $L$, and the remaining blocks keep their edges since the remainder is an induced subgraph. It is the extension step used to derive claim $(z1)$ from claim $(z8)$ in Kelmans's Theorem 3.1.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, pp. 7-8, Theorem 3.1, derivation of (z1) from (z8).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

theorem kelmans_p3_factor_extend : ∀ (W : Type) [Fintype W], ∀ G : SimpleGraph W, ∀ L : P3Path G, Nonempty (P3Factor (eraseP3 G L)) → Nonempty (P3Factor G) := by sorry

end CubicP3Partition
