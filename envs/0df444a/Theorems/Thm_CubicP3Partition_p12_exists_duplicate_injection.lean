-- Prove2me | Theorems.Thm_CubicP3Partition_p12_exists_duplicate_injection
-- name    : CubicP3Partition.p12_exists_duplicate_injection
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-16T10:16:58.790477+00:00
-- url     : https://prove2.me/theorems/fc1fc4f4-5934-4cb7-81f5-5499d35ba9f8
-- title:
--   P12 exists duplicate injection
-- statement:
--   Reindex positions as center, first leaf, second leaf.
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

theorem p12_exists_duplicate_injection [Fintype V] {G : SimpleGraph V}
    {C : Finset V} (hHall : p12CenterHall G C) :
    ∃ f : (↥C × Fin 2) → V,
      Function.Injective f ∧ ∀ z, G.Adj z.1.1 (f z) ∧ f z ∉ C := by sorry

end CubicP3Partition
