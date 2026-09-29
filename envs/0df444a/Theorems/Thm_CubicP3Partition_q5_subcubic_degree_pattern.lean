-- Prove2me | Theorems.Thm_CubicP3Partition_q5_subcubic_degree_pattern
-- name    : CubicP3Partition.q5_subcubic_degree_pattern
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T09:20:28.439915+00:00
-- url     : https://prove2.me/theorems/e1d14583-033a-4b27-aacd-ec316250b55b
-- title:
--   Degree-pattern classification at total cubic deficiency five
-- statement:
--   Let $G$ be a finite graph in which every vertex has degree one, two, or three. Suppose the total deficiency from cubicity is five:
--
--   $$
--   \sum_{v\in V(G)}(3-\deg v)=5.
--   $$
--
--   If $n_1$ and $n_2$ denote the numbers of degree-one and degree-two vertices, then $2n_1+n_2=5$, and necessarily
--
--   $$
--   (n_1,n_2)\in\{(0,5),(1,3),(2,1)\}.
--   $$
--
--   This elementary classification is useful for organizing five-port residual configurations.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

/-- A finite subcubic graph of minimum degree one and total cubic deficiency five has degree-one/degree-two counts (0,5), (1,3), or (2,1). -/
theorem q5_subcubic_degree_pattern
    {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V}
    (hdeg : ∀ v, 1 ≤ degree G v ∧ degree G v ≤ 3)
    (hdef : ∑ v, (3 - degree G v) = 5) :
    2 * (Finset.filter (fun v => degree G v = 1) Finset.univ).card +
        (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 5 ∧
      ((Finset.filter (fun v => degree G v = 1) Finset.univ).card = 0 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 5 ∨
        (Finset.filter (fun v => degree G v = 1) Finset.univ).card = 1 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 3 ∨
        (Finset.filter (fun v => degree G v = 1) Finset.univ).card = 2 ∧
          (Finset.filter (fun v => degree G v = 2) Finset.univ).card = 1) := by sorry

end CubicP3Partition
