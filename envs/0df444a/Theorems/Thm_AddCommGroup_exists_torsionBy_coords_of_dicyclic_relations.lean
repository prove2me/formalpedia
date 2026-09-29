-- Prove2me | Theorems.Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations
-- name    : AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/64e9905e-22e6-5de7-b2c7-b14e0c0d73e0
-- title:
--   M-torsion free of rank one over ℤ[β]/M and ℤ[α]/M
-- statement:
--   Let $M$ be a nonzero natural number with $3 \nmid M$, and let $A$ be an additive abelian group, viewed as a $\mathbb{Z}$-module, whose $M$-torsion submodule $\{T \in A : M \cdot T = 0\}$ is assumed to admit an isomorphism of additive groups $e$ with $\mathbb{Z}/M \times \mathbb{Z}/M$. Let $\alpha, \beta : A \to A$ be additive endomorphisms satisfying, for all $T \in A$, the relations $\alpha(\alpha T) = -T$, $\beta(\beta T) + \beta T + T = 0$ and $\alpha(\beta T) = \beta(\beta(\alpha T))$. The conclusion is a conjunction of two existence statements. First, there is $P \in A$ with $M \cdot P = 0$ such that every $T \in A$ with $M \cdot T = 0$ is of the form $T = c_1 \cdot P + c_2 \cdot \beta(P)$ for a unique pair $(c_1, c_2) \in \mathbb{Z}/M \times \mathbb{Z}/M$, the scalars acting through the canonical representatives in $\{0, \dots, M-1\}$ of $c_1$ and $c_2$. Second, the same holds with $\beta$ replaced by $\alpha$, for a (possibly different) point $P$ killed by $M$. Thus the $M$-torsion of $A$ is free of rank one both over $\mathbb{Z}[\beta]/M$ and over $\mathbb{Z}[\alpha]/M$.
--
--   The relations imposed on $\alpha$ and $\beta$ are those of generators of the dicyclic group of order $12$, realised as the automorphism group of the supersingular curve $y^2 = x^3 - x$ in characteristic $3$; the statement provides, for $M$ coprime to $3$, a basis of the $M$-torsion adapted either to the order-four automorphism (giving a $\mathbb{Z}[i]/M$-structure) or to the order-three one (giving a $\mathbb{Z}[\zeta_3]/M$-structure). It is used in the characteristic-three analysis of torsion bases on curves with $j = 0$ and in the associated counting of orders of $q$-expansions on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_exists_torsionBy_coords_of_dicyclic_relations.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations
    (M : ℕ) [NeZero M] (hM : ¬ 3 ∣ M) {A : Type*} [AddCommGroup A]
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M)
    (α β : A →+ A) (hα : ∀ T, α (α T) = -T) (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T))) :
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • β P = T) ∧
    (∃ P : A, (M : ℤ) • P = 0 ∧ ∀ T : A, (M : ℤ) • T = 0 →
      ∃! c : ZMod M × ZMod M, c.1.val • P + c.2.val • α P = T) := by sorry
