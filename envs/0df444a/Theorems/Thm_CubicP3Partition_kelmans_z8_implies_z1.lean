-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_z8_implies_z1
-- name    : CubicP3Partition.kelmans_z8_implies_z1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-07T21:26:58.587671+00:00
-- url     : https://prove2.me/theorems/b244a823-a82c-47d5-9447-37fd89553527
-- title:
--   Kelmans Theorem 3.1: $(z8) \Rightarrow (z1)$
-- statement:
--   For finite simple cubic 3-connected graphs whose order is divisible by six, if deleting the vertices of any specified three-vertex path from any such graph leaves an induced graph with a $P_3$-factor (claim $(z8)$), then every such graph has a $P_3$-factor (claim $(z1)$). This is the reverse direction of the $(z1)$-$(z8)$ equivalence in Kelmans's Theorem 3.1.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, pp. 7-8, Theorem 3.1, claims (z1) and (z8).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

theorem kelmans_z8_implies_z1 : ClaimZ8 -> ClaimZ1 := by sorry

end CubicP3Partition
