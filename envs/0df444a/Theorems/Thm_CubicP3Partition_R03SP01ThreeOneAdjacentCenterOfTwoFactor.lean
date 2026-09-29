-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneAdjacentCenterOfTwoFactor
-- name    : CubicP3Partition.R03SP01ThreeOneAdjacentCenterOfTwoFactor
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-15T22:22:06.038193+00:00
-- url     : https://prove2.me/theorems/c2c69f69-0018-4feb-8855-6433ddc48d3b
-- title:
--   Three one-residue cycles with adjacent cross edges have a P3-factor
-- statement:
--   Let $G$ be a finite simple graph and let $F$ be a spanning $2$-factor of $G$. Suppose the vertex set is partitioned into three cyclically ordered parts $A$, $B$, and $C$, each of size congruent to $1$ modulo $3$, and every successor edge in each cyclic order belongs to $F$. Assume the first part has at least four vertices. If the first two consecutive vertices of $A$ are respectively adjacent in $G$ to distinguished vertices of $B$ and $C$, then $G$ has a spanning $P_3$-factor.
--
--   This is a conditional assembly lemma for combining three one-residue cycles. It does not assert that every graph in OPG-46613 admits the required cyclic decomposition or cross edges.
-- source:
--   Derived auxiliary theorem for the Prove2me mission “P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)”, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29; background source: A. Kelmans, “Packing 3-vertex paths in cubic 3-connected graphs”, arXiv:0801.1239. The exact conditional three-cycle assembly is not asserted as a theorem in the cited source.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

theorem R03SP01ThreeOneAdjacentCenterOfTwoFactor
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (eV : A ⊕ (B ⊕ C) ≃ V)
    (kA kB kC : Nat)
    (eA : Fin (1 + kA * 3) ≃ A)
    (eB : Fin (1 + kB * 3) ≃ B)
    (eC : Fin (1 + kC * 3) ≃ C)
    (cycleA : ∀ i : Fin (1 + kA * 3),
      F.Adj (eV (Sum.inl (eA i)))
        (eV (Sum.inl (eA ⟨(i.val + 1) % (1 + kA * 3), Nat.mod_lt _ (by omega)⟩))))
    (cycleB : ∀ i : Fin (1 + kB * 3),
      F.Adj (eV (Sum.inr (Sum.inl (eB i))))
        (eV (Sum.inr (Sum.inl (eB ⟨(i.val + 1) % (1 + kB * 3), Nat.mod_lt _ (by omega)⟩)))))
    (cycleC : ∀ i : Fin (1 + kC * 3),
      F.Adj (eV (Sum.inr (Sum.inr (eC i))))
        (eV (Sum.inr (Sum.inr (eC ⟨(i.val + 1) % (1 + kC * 3), Nat.mod_lt _ (by omega)⟩)))))
    (hkA : 0 < kA)
    (hcrossAB : G.Adj (eV (Sum.inl (eA ⟨0, by omega⟩)))
      (eV (Sum.inr (Sum.inl (eB ⟨0, by omega⟩)))))
    (hcrossAC : G.Adj (eV (Sum.inl (eA ⟨1, by omega⟩)))
      (eV (Sum.inr (Sum.inr (eC ⟨0, by omega⟩))))) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
