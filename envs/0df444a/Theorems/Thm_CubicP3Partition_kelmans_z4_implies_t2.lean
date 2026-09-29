-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_z4_implies_t2
-- name    : CubicP3Partition.kelmans_z4_implies_t2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T23:23:28.821359+00:00
-- url     : https://prove2.me/theorems/8fbbf2fe-9e7e-4d58-8159-f31d937cfd6c
-- title:
--   Kelmans Theorem 3.1 via 3.11: $(z4) \Rightarrow (t2)$
-- statement:
--   If every vertex of every cubic 3-connected graph of order divisible by six centers a deletable 3-vertex path, then deleting the endpoints of any edge of a cubic 3-connected graph of order $2 \bmod 6$ leaves a graph with a $P_3$-factor. This is the $(z4) \Rightarrow (t2)$ step of Kelmans Theorem 3.1, proved in Section 3.11 (p2) with the $Y$-gadget of Figure 2.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, Theorem 3.1 and 3.11, claims (z4) and (t2).

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_kelmans_aux_claims

namespace CubicP3Partition

theorem kelmans_z4_implies_t2 : ClaimZ4 -> ClaimT2 := by sorry

end CubicP3Partition
