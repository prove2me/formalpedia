-- Prove2me | Theorems.Thm_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen
-- name    : AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/12512aae-d558-5a88-a15a-025da732fe10
-- title:
--   Morphisms to Proj agreeing locally on homogeneous charts coincide
-- statement:
--   Let $A$ be a commutative ring graded by a family $\mathcal A : \mathbb N \to \sigma$ of additive subgroups making $A$ a graded ring, let $W$ be a scheme, and let $a, b : W \to \operatorname{Proj}\mathcal A$ be two morphisms of schemes. Assume that for every point $w$ of $W$ there are a natural number $n$, an element $r \in A$ with $n > 0$ and $r \in \mathcal A_n$, together with an equality $a^{-1}D_+(r) = b^{-1}D_+(r)$ of the preimages in $W$ of the basic open $D_+(r) \subseteq \operatorname{Proj}\mathcal A$, such that $w \in a^{-1}D_+(r)$ and such that, for every element $x$ of the degree-zero homogeneous localisation `Away 𝒜 r`, the two induced maps on sections $\Gamma(D_+(r), \mathcal O_{\operatorname{Proj}\mathcal A}) \to \Gamma(a^{-1}D_+(r), \mathcal O_W)$ — that of $a$ along the identity inclusion $a^{-1}D_+(r) \subseteq a^{-1}D_+(r)$ and that of $b$ along the inclusion given by the above equality — take the same value on the canonical section `Proj.awayToSection 𝒜 r x` of $\mathcal O_{\operatorname{Proj}\mathcal A}$ over $D_+(r)$. Then $a = b$.
--
--   This is the uniqueness half of the standard recipe for describing morphisms into $\operatorname{Proj}$ of a graded ring through the homogeneous charts $D_+(r) \cong \operatorname{Spec}(A_r)_0$: a morphism to $\operatorname{Proj}$ is pinned down by its chart preimages together with the ring maps it induces on the degree-zero localisations. It is used in the construction of the canonical morphism to $\operatorname{Proj}$ attached to a section ring, via [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_isCanonicalToProj).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

theorem AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {W : Scheme.{u}} (a b : W ⟶ Proj 𝒜)
    (h : ∀ w : W, ∃ (n : ℕ) (r : A) (hn : 0 < n) (hr : r ∈ 𝒜 n)
      (e : a ⁻¹ᵁ Proj.basicOpen 𝒜 r = b ⁻¹ᵁ Proj.basicOpen 𝒜 r),
      w ∈ a ⁻¹ᵁ Proj.basicOpen 𝒜 r ∧
        ∀ x : Away 𝒜 r,
          a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl (Proj.awayToSection 𝒜 r x) =
            b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le (Proj.awayToSection 𝒜 r x)) :
    a = b := by sorry
