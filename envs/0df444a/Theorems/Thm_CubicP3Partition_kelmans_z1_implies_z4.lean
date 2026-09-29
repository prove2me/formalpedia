-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_z1_implies_z4
-- name    : CubicP3Partition.kelmans_z1_implies_z4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T23:23:26.30956+00:00
-- url     : https://prove2.me/theorems/159ea234-237c-4b75-92ed-375a5b2c18ff
-- title:
--   Kelmans Theorem 3.1 via 3.8: $(z1) \Rightarrow (z4)$
-- statement:
--   If every cubic 3-connected graph of order divisible by six has a $P_3$-factor, then for every such graph and every vertex $x$ there is a 3-vertex path centered at $x$ whose deletion leaves a graph with a $P_3$-factor. This is the $(z1) \Rightarrow (z4)$ step of Kelmans Theorem 3.1, proved in Section 3.8 via a $K_{3,3}$ blow-up: a counterexample vertex that is an endpoint in every factor lifts to a cubic 3-connected graph with no factor at all.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, Theorem 3.1 and 3.8, claims (z1) and (z4).

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_kelmans_aux_claims

namespace CubicP3Partition

theorem kelmans_z1_implies_z4 : ClaimZ1 -> ClaimZ4 := by sorry

end CubicP3Partition
