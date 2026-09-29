-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
-- name    : AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/c2af8e1e-9cdf-5c6b-a175-88591e176d14
-- title:
--   Smooth proper model covering the k-points of an affine curve
-- statement:
--   Let $k$ be an algebraically closed field, let $Y$ be a scheme and let $y \colon Y \to \operatorname{Spec} k$ be a proper morphism. Let $A$ be a commutative $k$-algebra which is an integral domain, of finite type over $k$, with $\operatorname{ringKrullDim} A = 1$, and let $\varphi \colon \operatorname{Spec} A \to Y$ be a morphism whose composite with $y$ is the morphism $\operatorname{Spec} A \to \operatorname{Spec} k$ induced by the structure map $k \to A$, so that $\varphi$ is a morphism of $k$-schemes. The assertion is that there exist a scheme $C$, a morphism $c \colon C \to \operatorname{Spec} k$ which is proper and smooth of relative dimension $1$, with $C$ an integral scheme, and a morphism $\psi \colon C \to Y$ whose composite with $y$ is $c$, such that the following holds: for every section $a \colon \operatorname{Spec} k \to \operatorname{Spec} A$ of the structure morphism $\operatorname{Spec} A \to \operatorname{Spec} k$ (that is, every $k$-point of $\operatorname{Spec} A$) there is a section $p \colon \operatorname{Spec} k \to C$ of $c$ with $p$ followed by $\psi$ equal to $a$ followed by $\varphi$. Thus every $k$-point of $Y$ in the image of the $k$-points of $\operatorname{Spec} A$ under $\varphi$ is also in the image of the $k$-points of $C$ under $\psi$; no relation between $C$ and $\operatorname{Spec} A$ beyond this is asserted.
--
--   This is the passage from an affine integral curve over an algebraically closed field to a smooth proper model mapping to the same proper target, in the weak form that records only agreement on $k$-rational points. It is used by [`AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem`](thm.html#AlgebraicGeometry.mem_of_isProper_of_forall_smoothProperCurve_mem), where membership statements for proper schemes are reduced to tests along smooth proper curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_smoothProperCurve_hom_comp_eq_of_ringKrullDim_eq_one
    {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
    [IsProper y] (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (hA : ringKrullDim A = 1) (φ : Spec (CommRingCat.of A) ⟶ Y)
    (hφ : φ ≫ y = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ (C : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of k)) (_ : IsProper c)
      (_ : SmoothOfRelativeDimension 1 c) (_ : IsIntegral C) (ψ : C ⟶ Y), ψ ≫ y = c ∧
      ∀ a : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A),
        a ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) = 𝟙 _ →
        ∃ p : Spec (CommRingCat.of k) ⟶ C, p ≫ c = 𝟙 _ ∧ p ≫ ψ = a ≫ φ := by sorry
