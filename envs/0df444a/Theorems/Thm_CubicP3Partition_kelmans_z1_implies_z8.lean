-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_z1_implies_z8
-- name    : CubicP3Partition.kelmans_z1_implies_z8
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T21:27:06.973299+00:00
-- url     : https://prove2.me/theorems/7e0c5eb4-b95c-442a-aa8f-8578a66ed4d7
-- title:
--   Kelmans Theorem 3.1: $(z1) \Rightarrow (z8)$
-- statement:
--   For finite simple cubic 3-connected graphs whose order is divisible by six, if every such graph has a $P_3$-factor (claim $(z1)$), then deleting the vertices of any specified three-vertex path from any such graph leaves an induced graph that has a $P_3$-factor (claim $(z8)$). This is the forward direction of the $(z1)$-$(z8)$ equivalence in Kelmans's Theorem 3.1.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, pp. 7-8, Theorem 3.1, claims (z1) and (z8).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

theorem kelmans_z1_implies_z8 : ClaimZ1 -> ClaimZ8 := by sorry

end CubicP3Partition
