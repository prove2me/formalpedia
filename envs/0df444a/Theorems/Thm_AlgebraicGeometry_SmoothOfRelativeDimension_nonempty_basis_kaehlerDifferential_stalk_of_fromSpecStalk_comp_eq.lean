-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
-- name    : AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/b7ec0fa1-3f1b-5e01-8b4e-6a6ee545804e
-- title:
--   Free differentials on stalks of a smooth R-scheme
-- statement:
--   Let $R$ be a commutative ring, $Y$ a scheme, and $f \colon Y \to \operatorname{Spec} R$ a morphism that is smooth of relative dimension $n$ for a natural number $n$ (in the sense of Mathlib's `SmoothOfRelativeDimension` instance class). Let $y$ be a point of $Y$, and suppose the local ring $\mathcal{O}_{Y,y} =$ `Y.presheaf.stalk y` is endowed with an $R$-algebra structure such that the composite of the canonical morphism $\operatorname{Spec} \mathcal{O}_{Y,y} \to Y$ with $f$ equals $\operatorname{Spec}$ of the structure map $R \to \mathcal{O}_{Y,y}$, i.e. the given algebra structure is the one induced by $f$. The conclusion is that the type of $\mathcal{O}_{Y,y}$-bases of the module of Kähler differentials $\Omega_{\mathcal{O}_{Y,y}/R}$ indexed by `Fin n` is nonempty; equivalently, $\Omega_{\mathcal{O}_{Y,y}/R}$ is a free $\mathcal{O}_{Y,y}$-module of rank $n$. Note that the assertion is the existence of such a basis (a `Nonempty` statement), not a designated choice of one.
--
--   This is the local form, over a general commutative ring base, of the statement that a smooth morphism of relative dimension $n$ has locally free differentials of rank $n$; it is the ring-base companion of the field-base version in which the stalk carries its canonical algebra structure. It feeds the construction of component data for smooth schemes in the Néron-model infrastructure, where the algebra structure on the stalk is carried as data and must be pinned to $f$ by the displayed equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothOfRelativeDimension_nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.SmoothOfRelativeDimension.nonempty_basis_kaehlerDifferential_stalk_of_fromSpecStalk_comp_eq
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f] (y : Y)
    [Algebra R (Y.presheaf.stalk y)]
    (halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) :
    Nonempty (Module.Basis (Fin n) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])) := by sorry
