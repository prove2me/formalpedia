-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_tower_baseChange_of_isPullback
-- name    : AlgebraicGeometry.exists_tower_baseChange_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/14c769ba-019e-594c-9be8-ddb0cf7ba7e2
-- title:
--   Base change of a π-adic tower with group action
-- statement:
--   Let $\mathcal O$ be a commutative ring and $\pi \in \mathcal O$, and write $\mathcal O_n := \mathcal O/(\pi^{n+1})$. Given a family of schemes $X_n$ ($n \in \mathbb N$), structure morphisms $xb_n : X_n \to \operatorname{Spec}\mathcal O_n$ and transition morphisms $xt_n : X_n \to X_{n+1}$ such that for every $n$ the square formed by $xt_n$, $xb_n$, $xb_{n+1}$ and the morphism $\operatorname{Spec}\mathcal O_n \to \operatorname{Spec}\mathcal O_{n+1}$ induced by the quotient map $\mathcal O_{n+1} \to \mathcal O_n$ is cartesian; and given a group $G$ together with, for each $n$, a group homomorphism $a_n : G \to \operatorname{Aut}(X_n)$ whose automorphisms lie over $\operatorname{Spec}\mathcal O_n$ (that is, $a_n(g)$ followed by $xb_n$ equals $xb_n$) and commute with the transitions ($a_n(g)$ followed by $xt_n$ equals $xt_n$ followed by $a_{n+1}(g)$); let finally $S$ be any commutative $\mathcal O$-algebra, and put $S_n := S/(\sigma^{n+1})$ with $\sigma$ the image of $\pi$ in $S$. Then there exist schemes $X'_n$, morphisms $xb'_n : X'_n \to \operatorname{Spec} S_n$ and $xt'_n : X'_n \to X'_{n+1}$, group homomorphisms $a'_n : G \to \operatorname{Aut}(X'_n)$ and morphisms $q_n : X'_n \to X_n$ such that: each square $(q_n, xb'_n, xb_n, \operatorname{Spec} S_n \to \operatorname{Spec}\mathcal O_n)$ is cartesian, the latter morphism coming from the map $\mathcal O_n \to S_n$ induced by $\mathcal O \to S$ (so $X'_n = X_n \times_{\operatorname{Spec}\mathcal O_n} \operatorname{Spec} S_n$); each square $(xt'_n, xb'_n, xb'_{n+1}, \operatorname{Spec} S_n \to \operatorname{Spec} S_{n+1})$ is cartesian; $xt'_n$ followed by $q_{n+1}$ equals $q_n$ followed by $xt_n$; $a'_n(g)$ followed by $q_n$ equals $q_n$ followed by $a_n(g)$; and the $a'_n(g)$ lie over $\operatorname{Spec} S_n$ and commute with the transitions $xt'_n$ in the same sense as for $X$.
--
--   This is the base-change construction for a $\pi$-adic tower of schemes carrying a compatible group action: the whole tower, its transition maps, its $G$-action and the projections to the original tower are produced simultaneously over the truncations $S/(\sigma^{n+1})$ of an arbitrary $\mathcal O$-algebra $S$. It is used in the Čerednik–Drinfeld part of the development, where [`CerednikDrinfeld.FormalOmega.MumfordTower.nonempty_nrPresentation`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.nonempty_nrPresentation) transports a presentation of a Mumford tower along a ring extension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_tower_baseChange_of_isPullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_tower_baseChange_of_isPullback
    (𝒪 : Type u) [CommRing 𝒪] (π : 𝒪)
    (X : ℕ → Scheme.{u}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (G : Type u) [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (S : Type u) [CommRing S] [Algebra 𝒪 S] :
    ∃ (X' : ℕ → Scheme.{u}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)})))
      (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1)) (a' : ∀ n : ℕ, G →* Aut (X' n)) (q : ∀ n : ℕ, X' n ⟶ X n),
      (∀ n : ℕ, IsPullback (q n) (xb' n) (xb n)
        (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) ∧
      (∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 S π) (Nat.le_succ (n + 1)))))))) ∧
      (∀ n : ℕ, xt' n ≫ q (n + 1) = q n ≫ xt n) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ q n = q n ≫ (a n g).hom) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n) ∧
      (∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom) := by sorry
