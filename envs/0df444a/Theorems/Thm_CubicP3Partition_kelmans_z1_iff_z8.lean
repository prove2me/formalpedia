-- Prove2me | Theorems.Thm_CubicP3Partition_kelmans_z1_iff_z8
-- name    : CubicP3Partition.kelmans_z1_iff_z8
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-07T03:05:54.695711+00:00
-- url     : https://prove2.me/theorems/56e0b93b-24d3-4e70-9976-d11a160641c8
-- title:
--   Kelmans Theorem 3.1: $(z1) \Leftrightarrow (z8)$
-- statement:
--   For finite simple cubic 3-connected graphs whose order is divisible by six, the following two universal claims are equivalent:
--
--   1. every such graph has a $P_3$-factor;
--   2. after deleting the vertices of any specified three-vertex path from any such graph, the remaining induced graph has a $P_3$-factor.
--
--   $$
--   (z1)\quad\Longleftrightarrow\quad(z8).
--   $$
--
--   This is the $(z1)$–$(z8)$ equivalence contained in Kelmans's larger list of equivalent claims.
--
--   **Formalization Note** Both sides quantify over ordinary small finite vertex types and use the mission's explicit noninduced path-factor and vertex-deletion models.
-- source:
--   A. Kelmans, Packing 3-vertex Paths In Cubic 3-connected Graphs, https://arxiv.org/abs/0910.2766v2, pp. 7–8, Theorem 3.1, claims (z1) and (z8).

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

/-- The equivalence between claims (z1) and (z8) from Kelmans's Theorem 3.1. -/
theorem kelmans_z1_iff_z8 : ClaimZ1 ↔ ClaimZ8 := by sorry

end CubicP3Partition
