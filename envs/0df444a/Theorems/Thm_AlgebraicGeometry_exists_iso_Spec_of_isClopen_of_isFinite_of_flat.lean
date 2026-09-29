-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat
-- name    : AlgebraicGeometry.exists_iso_Spec_of_isClopen_of_isFinite_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/60070364-9ca6-53ff-86df-db4a625180a0
-- title:
--   A clopen piece of a finite flat scheme is affine and flat
-- statement:
--   Let $S$ be a commutative ring, $K$ a scheme, and $p : K \to \operatorname{Spec} S$ a morphism that is finite (`IsFinite`) and flat (`Flat`), both as typeclass hypotheses on $p$. Let $\mathcal G$ be an open subscheme of $K$ (an element of `K.Opens`) whose underlying subset of $K$ is in addition closed. Then there exist a type $S'$, a commutative ring structure on it, a ring homomorphism $\varphi : S \to S'$, and an isomorphism of schemes $e : \operatorname{Spec} S' \cong \mathcal G$ such that three conditions hold: first, $e$ followed by the canonical open immersion $\mathcal G \hookrightarrow K$ followed by $p$ equals $\operatorname{Spec}(\varphi)$, i.e. the structure morphism of $\mathcal G$ over $\operatorname{Spec} S$ is identified, through $e$, with the morphism of affine schemes induced by $\varphi$; second, $\operatorname{Spec}(\varphi)$ is flat; third, if the composite $\mathcal G \hookrightarrow K \to \operatorname{Spec} S$ is surjective, then so is $\operatorname{Spec}(\varphi)$. Thus the clopen piece $\mathcal G$ is presented as the spectrum of a flat $S$-algebra, compatibly with the projections to $\operatorname{Spec} S$.
--
--   This is the standard fact that an open and closed subscheme of a scheme finite over an affine base is itself affine and flat over that base, packaged so that the clopen piece comes with an explicit presentation as $\operatorname{Spec}$ of an $S$-algebra. It is used in the construction of flat surjective covers carrying full level structures on fake elliptic curves, with $\mathcal G$ the locus where a section generates the $\mathfrak m$-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_iso_Spec_of_isClopen_of_isFinite_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_Spec_of_isClopen_of_isFinite_of_flat
    {S : Type u} [CommRing S] {K : Scheme.{u}} (p : K ⟶ Spec (CommRingCat.of S)) [IsFinite p] [Flat p]
    (𝒢 : K.Opens) (h𝒢 : IsClosed (𝒢 : Set ↥K)) :
    ∃ (S' : Type u) (_ : CommRing S') (φ : S →+* S') (e : Spec (CommRingCat.of S') ≅ (𝒢 : Scheme.{u})),
      e.hom ≫ 𝒢.ι ≫ p = Spec.map (CommRingCat.ofHom φ) ∧
      Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      (Surjective (𝒢.ι ≫ p) → Surjective (Spec.map (CommRingCat.ofHom φ))) := by sorry
