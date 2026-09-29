-- Prove2me | Theorems.Thm_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor
-- name    : AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/662ae1a1-8648-5158-a6d9-f231f1a9235e
-- title:
--   Locally of finite type from factorisation through f.g. subalgebras
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\xi \colon X \to \operatorname{Spec} R$ a morphism. Assume the following: for every commutative ring $A$ carrying an $R$-algebra structure and every morphism $\varphi \colon \operatorname{Spec} A \to X$ which is a morphism over $\operatorname{Spec} R$, in the sense that $\varphi$ followed by $\xi$ equals $\operatorname{Spec}$ of the structure map $R \to A$, there exist an $R$-subalgebra $A_0 \subseteq A$ which is finitely generated as an $R$-algebra and a morphism $\varphi_0 \colon \operatorname{Spec} A_0 \to X$ such that $\varphi_0$ followed by $\xi$ equals $\operatorname{Spec}$ of the structure map $R \to A_0$, and such that $\operatorname{Spec}$ of the inclusion $A_0 \hookrightarrow A$ followed by $\varphi_0$ equals $\varphi$. The conclusion is that $\xi$ is locally of finite type. Note that, besides the factorisation of $\varphi$, the hypothesis demands that the intermediate morphism $\varphi_0$ itself be a morphism over $\operatorname{Spec} R$.
--
--   This is the "locally of finite type" half of the converse direction in the characterisation of morphisms locally of finite presentation by their functor of points (EGA IV 8.14.2), specialised to the cofiltered system of finitely generated $R$-subalgebras $A_0$ of an $R$-algebra $A$, whose limit is $\operatorname{Spec} A$. It is used to verify the finite-type property of a relative Picard-type moduli morphism presented by such a factorisation property.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_AffineLimit_locallyOfFiniteType_of_forall_exists_fg_factor.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.AffineLimit.locallyOfFiniteType_of_forall_exists_fg_factor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (ξ : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (A : Type u) [CommRing A] [Algebra R A] (φ : Spec (CommRingCat.of A) ⟶ X),
      φ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R A)) →
      ∃ (A₀ : Subalgebra R A) (_ : A₀.FG) (φ₀ : Spec (CommRingCat.of ↥A₀) ⟶ X),
        φ₀ ≫ ξ = Spec.map (CommRingCat.ofHom (algebraMap R ↥A₀)) ∧
        Spec.map (CommRingCat.ofHom A₀.val.toRingHom) ≫ φ₀ = φ) :
    LocallyOfFiniteType ξ := by sorry
