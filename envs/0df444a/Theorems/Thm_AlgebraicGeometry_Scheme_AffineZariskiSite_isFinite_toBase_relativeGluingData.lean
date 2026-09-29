-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData
-- name    : AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/13a72606-3742-507f-bdb9-a9c3e5cd98e2
-- title:
--   Relative spectrum of a module-finite algebra is finite
-- statement:
--   Let $X$ be a scheme, let $F$ be a functor from the opposite of the affine Zariski site of $X$ (the affine opens of $X$, ordered by inclusion) to commutative rings, and let $\alpha$ be a natural transformation from the composite of the opposite of the inclusion functor `Scheme.AffineZariskiSite.toOpensFunctor X` with the structure presheaf of $X$ — that is, from the presheaf $U \mapsto \Gamma(U, \mathcal O_X)$ on affine opens — to $F$. Assume $\alpha$ is coequifibered, so that $F$ together with $\alpha$ presents a quasi-coherent $\mathcal O_X$-algebra: its values on basic opens are the corresponding localisations. Assume further that for every affine open $U$ of $X$ the ring homomorphism $\alpha_U \colon \Gamma(U,\mathcal O_X) \to F(U)$ is finite, i.e. $F(U)$ is a finitely generated $\Gamma(U,\mathcal O_X)$-module. The conclusion is that the structure morphism to $X$ of the scheme obtained from the associated relative gluing data, namely `(Scheme.AffineZariskiSite.relativeGluingData H).toBase`, the relative spectrum $\operatorname{Spec}_X F \to X$ glued from the affine morphisms $\operatorname{Spec} F(U) \to U$, is a finite morphism of schemes.
--
--   This is the standard statement that the relative spectrum of a quasi-coherent $\mathcal O_X$-algebra which is module-finite over $\mathcal O_X$ is a finite $X$-scheme. It is used to convert a finite quasi-coherent algebra, such as one produced by an algebraisation argument, into a finite morphism of schemes, and is invoked in the results on $\mathcal O$-module presheaves over proper morphisms that concern comparison of sections and of divided powers of ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData
    {X : Scheme.{u}} {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)
    (hfin : ∀ U : X.AffineZariskiSite, (α.app (op U)).hom.Finite) :
    IsFinite (Scheme.AffineZariskiSite.relativeGluingData H).toBase := by sorry
