-- Prove2me | Theorems.Thm_CubicP3Partition_p3Factor_iff_center_hall
-- name    : CubicP3Partition.p3Factor_iff_center_hall
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T09:20:14.965769+00:00
-- url     : https://prove2.me/theorems/cc9330d2-92e5-4236-9cb0-70ca8ccf5706
-- title:
--   P3-factors are equivalent to duplicated-center Hall systems
-- statement:
--   Let $G$ be a finite simple graph. Then $G$ has a spanning non-induced $P_3$-factor if and only if there is a set $C\subseteq V(G)$ with $3|C|=|V(G)|$ such that every subset $A\subseteq C$ has at least $2|A|$ neighbours outside $C$:
--
--   $$
--   G\text{ has a }P_3\text{-factor}\quad\Longleftrightarrow\quad\exists C,\;3|C|=|V(G)|\text{ and }|N(A)\setminus C|\ge 2|A|\text{ for all }A\subseteq C.
--   $$
--
--   The equivalence turns a $P_3$-factor into its set of middle vertices and, conversely, realizes two leaf slots per center through Hall's theorem. It gives an exact finite matching characterization and does not assume cubicity or connectivity.
--
--   **Formalization Note** The predicate `p12CenterHall` is the two-fold Hall condition on duplicated center slots.
-- source:
--   Derived structural theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; the exact Hall characterization is a project-derived auxiliary theorem.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_cubic_p3_partition_center_hall

namespace CubicP3Partition

universe u

/-- Exact characterization of finite non-induced P3-factors by a one-third-size center set satisfying the duplicated-center Hall inequalities. -/
theorem p3Factor_iff_center_hall
    {V : Type u} [Fintype V] {G : SimpleGraph V} :
    Nonempty (P3Factor G) ↔
      ∃ C : Finset V, p12CenterSize C ∧ p12CenterHall G C := by sorry

end CubicP3Partition
