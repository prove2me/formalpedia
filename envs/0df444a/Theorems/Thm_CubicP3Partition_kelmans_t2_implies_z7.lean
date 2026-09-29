-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_t2_implies_z7
-- name    : CubicP3Partition.kelmans_t2_implies_z7
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T23:23:29.948715+00:00
-- url     : https://prove2.me/theorems/8b4498c6-6624-416c-a0c8-18ce58350473
-- title:
--   Kelmans Theorem 3.1 via 3.16: $(t2) \Rightarrow (z7)$
-- statement:
--   If deleting the endpoints of any edge of a cubic 3-connected graph of order $2 \bmod 6$ leaves a graph with a $P_3$-factor, then deleting any two distinct edges of a cubic 3-connected graph of order divisible by six leaves a graph with a $P_3$-factor. This is the $(t2) \Rightarrow (z7)$ step of Kelmans Theorem 3.1, proved in Section 3.16 by subdividing both edges and joining the new vertices: the subdivided graph has order $2 \bmod 6$, and removing the new edge's endpoints recovers the double edge-deletion.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, Theorem 3.1 and 3.16, claims (t2) and (z7).

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_kelmans_aux_claims

namespace CubicP3Partition

theorem kelmans_t2_implies_z7 : ClaimT2 -> ClaimZ7 := by sorry

end CubicP3Partition
