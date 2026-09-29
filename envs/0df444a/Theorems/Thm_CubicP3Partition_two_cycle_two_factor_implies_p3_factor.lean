-- Prove2me | Theorems.Thm_CubicP3Partition_two_cycle_two_factor_implies_p3_factor
-- name    : CubicP3Partition.two_cycle_two_factor_implies_p3_factor
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-15T21:35:29.924561+00:00
-- url     : https://prove2.me/theorems/ece5a5bd-e2b7-4e9e-ac4a-dfe7878b7b19
-- title:
--   A two-cycle spanning 2-factor yields a P3-factor at divisible order
-- statement:
--   Let $G$ be a finite connected simple graph and let $F$ be a spanning $2$-factor of $G$. Suppose $F$ has exactly two distinct connected components, represented by cycles $C_A$ and $C_B$, and their supports cover every vertex of $G$. If the total order is divisible by three, then $G$ admits a spanning $P_3$-factor:
--
--   $$
--   3\mid |V(G)| \quad\Longrightarrow\quad G\text{ has a }P_3\text{-factor}.
--   $$
--
--   This is a reusable sufficient condition for the P3-Partitions of Cubic 3-Connected Graphs mission. It does not assert that every graph in that mission has a spanning $2$-factor with exactly two components.
-- source:
--   Derived auxiliary theorem for the Prove2me mission “P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)”, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background source: A. Kelmans, “Packing 3-vertex paths in cubic 3-connected graphs”, arXiv:0801.1239. The exact two-component 2-factor condition is not asserted as a theorem in the cited source.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

/-- A connected graph with a spanning two-factor having exactly two components and order divisible by three has a non-induced P3-factor. -/
theorem two_cycle_two_factor_implies_p3_factor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB : F.ConnectedComponent)
    (hneq : cA ≠ cB)
    (hcover : ∀ v : V, v ∈ cA.supp ∨ v ∈ cB.supp)
    [Fintype cA.supp] [Fintype cB.supp]
    (horder : 3 ∣ Fintype.card V)
    (hconn : G.Connected) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
