-- Prove2me | Theorems.Thm_CubicP3Partition_hamiltonian_graph_p3Factor_general
-- name    : CubicP3Partition.hamiltonian_graph_p3Factor_general
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-15T21:35:24.005231+00:00
-- url     : https://prove2.me/theorems/dcabbdab-d323-4bfb-8f3d-678c198ac2d1
-- title:
--   Hamiltonian graphs of order divisible by three have a P3-factor
-- statement:
--   Let $G$ be a finite simple Hamiltonian graph. If its number of vertices is divisible by three, then $G$ admits a spanning $P_3$-factor: there is a family of vertex-disjoint paths on three vertices whose vertex sets partition $V(G)$. In symbols,
--
--   $$
--   3\mid |V(G)| \quad\Longrightarrow\quad G\text{ has a }P_3\text{-factor}.
--   $$
--
--   This gives a reusable sufficient condition for the P3-Partitions of Cubic 3-Connected Graphs mission. It does not assert that every graph in that mission is Hamiltonian.
-- source:
--   Derived auxiliary theorem for the Prove2me mission “P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)”, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background source: A. Kelmans, “Packing 3-vertex paths in cubic 3-connected graphs”, arXiv:0801.1239. The auxiliary Hamiltonian condition is not asserted as a theorem in the cited source.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

/-- A finite Hamiltonian graph of order divisible by three has a non-induced P3-factor. -/
theorem hamiltonian_graph_p3Factor_general
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hHamiltonian : G.IsHamiltonian)
    (hOrder : 3 ∣ Fintype.card V) : Nonempty (P3Factor G) := by sorry

end CubicP3Partition
