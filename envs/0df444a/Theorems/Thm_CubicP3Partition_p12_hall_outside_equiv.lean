-- Prove2me | Theorems.Thm_CubicP3Partition_p12_hall_outside_equiv
-- name    : CubicP3Partition.p12_hall_outside_equiv
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:55.479767+00:00
-- url     : https://prove2.me/theorems/b453b0c0-a60b-4bf1-bf63-967b7f9811c2
-- title:
--   P12 hall outside equiv
-- statement:
--   Hall plus the one-third size equation gives a bijection to the outside vertices.
--
--   $$|A|\le |N_{\mathrm{dup}}(A)|.$ $
--
--   This isolates one reusable step in the exact duplicated-center Hall characterization of finite non-induced $P_3$-factors. It is an auxiliary theorem and does not assert the open root P3-factor conjecture.
-- source:
--   Derived auxiliary theorem for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background: A. Kelmans, ‘Packing 3-vertex paths in cubic 3-connected graphs’, arXiv:0801.1239.

import Definitions.Def_cubic_p3_partition_center_hall_aux

namespace CubicP3Partition

universe u

variable {V : Type u}

theorem p12_hall_outside_equiv [Fintype V] {G : SimpleGraph V}
    {C : Finset V} (hSize : p12CenterSize C)
    (hHall : p12CenterHall G C) :
    ∃ e : (↥C × Fin 2) ≃ {w : V // w ∉ C},
      ∀ z, G.Adj z.1.1 (e z).1 := by sorry

end CubicP3Partition
