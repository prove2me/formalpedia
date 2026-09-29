-- Prove2me | Theorems.Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit
-- name    : AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/3ef93d66-b08f-5869-8e98-2c974168b91a
-- title:
--   Limit criterion for local finite presentation over an affine base
-- statement:
--   Let $\mathcal O$ be a commutative ring, $M$ a scheme and $\pi_M : M \to \operatorname{Spec}\mathcal O$ a morphism of schemes (the target being the spectrum of $\mathcal O$ viewed as an object of $\mathsf{CommRingCat}$). Assume the following hypothesis $H$: for every type $\iota$ carrying a preorder, non-empty and directed upwards, every family $(S_i)_{i\in\iota}$ of commutative rings equipped with $\mathcal O$-algebra structures, every family of $\mathcal O$-algebra maps $t_{ij} : S_i \to S_j$ indexed by proofs of $i \le j$ with $t_{ii} = \mathrm{id}$ and $t_{jk}\circ t_{ij} = t_{ik}$, and every $\mathcal O$-algebra $L$ with $\mathcal O$-algebra maps $c_i : S_i \to L$ satisfying $c_j \circ t_{ij} = c_i$, such that every $x \in L$ is of the form $c_i(y)$ for some $i$ and some $y \in S_i$, and such that $c_i(y) = c_i(z)$ implies $t_{ij}(y) = t_{ij}(z)$ for some $j \ge i$, both of the following hold: (A) every morphism $x : \operatorname{Spec} L \to M$ with $x$ followed by $\pi_M$ equal to $\operatorname{Spec}$ of the structure map $\mathcal O \to L$ factors as $\operatorname{Spec}(c_i)$ followed by some $x_i : \operatorname{Spec} S_i \to M$ lying over $\operatorname{Spec}$ of $\mathcal O \to S_i$, for some $i$; and (B) if $x_i, y_i : \operatorname{Spec} S_i \to M$ both lie over $\operatorname{Spec}$ of $\mathcal O \to S_i$ and become equal after precomposition with $\operatorname{Spec}(c_i)$, then they become equal after precomposition with $\operatorname{Spec}(t_{ij})$ for some $j \ge i$. Then $\pi_M$ satisfies `LocallyOfFinitePresentation`.
--
--   This is Grothendieck's limit criterion recognising a morphism as locally of finite presentation from its functor of points on filtered colimits of rings, specialised to an affine base and with the colimit described by the two elementary properties (every element comes from some stage; equality is detected at some later stage) rather than by a chosen model, so that it can be instantiated with any presentation of the colimit. It is used to establish local finite presentation of the structure morphism of the quaternionic moduli problems, via [`CerednikDrinfeld.QM.IsFineModuli.locallyOfFinitePresentation`](thm.html#CerednikDrinfeld.QM.IsFineModuli.locallyOfFinitePresentation) and [`CerednikDrinfeld.QM.IsFineModuliT.locallyOfFinitePresentation`](thm.html#CerednikDrinfeld.QM.IsFineModuliT.locallyOfFinitePresentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_locallyOfFinitePresentation_of_forall_directed_colimit.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.locallyOfFinitePresentation_of_forall_directed_colimit
    {𝒪 : Type u} [CommRing 𝒪] {M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (H : ∀ (ι : Type u) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
      (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra 𝒪 (S i)]
      (t : ∀ i j, i ≤ j → (S i →ₐ[𝒪] S j))
      (_ : ∀ i (h : i ≤ i), t i i h = AlgHom.id 𝒪 (S i))
      (_ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
      (L : Type u) [CommRing L] [Algebra 𝒪 L] (c : ∀ i, S i →ₐ[𝒪] L)
      (_ : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
      (_ : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
      (_ : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z),
      (∀ x : Spec (CommRingCat.of L) ⟶ M, x ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 L)) →
          ∃ (i : ι) (xi : Spec (CommRingCat.of (S i)) ⟶ M), xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) ∧
            x = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi) ∧
      (∀ (i : ι) (xi yi : Spec (CommRingCat.of (S i)) ⟶ M),
          xi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) → yi ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S i))) →
          Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (c i).toRingHom) ≫ yi →
          ∃ (j : ι) (h : i ≤ j), Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ xi = Spec.map (CommRingCat.ofHom (t i j h).toRingHom) ≫ yi)) :
    LocallyOfFinitePresentation πM := by sorry
