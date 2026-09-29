-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_etale_nhd_section_of_smooth
-- name    : AlgebraicGeometry.exists_etale_nhd_section_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/1c1530de-75be-5ab9-a7c7-b705c1a0ec51
-- title:
--   Étale neighbourhood sections of a smooth morphism through a residue point
-- statement:
--   Let $R$ be a commutative local ring (in universe $u$) with maximal ideal $\mathfrak m$ and residue field $k = R/\mathfrak m$, let $U$ be a scheme, let $f \colon U \to \operatorname{Spec} R$ be a smooth morphism, and let $x \colon \operatorname{Spec} k \to U$ be a point of the closed fibre, i.e. $x$ followed by $f$ equals $\operatorname{Spec}$ of the residue homomorphism $R \to k$. The assertion is that there exist a type $E$ in the same universe carrying a commutative ring structure and an $R$-algebra structure, such that $E$ is étale over $R$ (`Algebra.Etale R E`), together with a maximal ideal $\mathfrak n \subseteq E$ whose contraction along $\operatorname{algebraMap} R E$ contains $\mathfrak m$, with the property that every $e \in E$ is congruent modulo $\mathfrak n$ to the image of some $r \in R$ (so the induced map $k \to E/\mathfrak n$ is surjective, and the residue extension at $\mathfrak n$ is trivial), and a morphism $\tau \colon \operatorname{Spec} E \to U$ such that $\tau$ followed by $f$ is $\operatorname{Spec}$ of $\operatorname{algebraMap} R E$, and such that $\operatorname{Spec}$ of the quotient map $E \to E/\mathfrak n$ followed by $\tau$ agrees with $\operatorname{Spec}$ of the induced map $k \to E/\mathfrak n$ followed by $x$.
--
--   This is the local, ring-theoretic form of the standard fact (EGA IV, 17.16.3) that a smooth morphism admits a section through a rational point of a fibre after an étale base change which is a neighbourhood of the corresponding point of the base, here with the étale neighbourhood $(E,\mathfrak n)$ realised as an étale $R$-algebra with trivial residue extension at $\mathfrak n$. It is used to prove [`AlgebraicGeometry.exists_section_comp_eq_of_smooth_of_henselianLocalRing`](thm.html#AlgebraicGeometry.exists_section_comp_eq_of_smooth_of_henselianLocalRing), where for a Henselian local base the étale neighbourhood splits off a copy of $R$ and the section descends to $\operatorname{Spec} R$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_etale_nhd_section_of_smooth.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_etale_nhd_section_of_smooth
    {R : Type u} [CommRing R] [IsLocalRing R]
    {U : Scheme.{u}} (f : U ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (x : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ U)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E) (_ : Algebra.Etale R E) (𝔫 : Ideal E) (_ : 𝔫.IsMaximal)
      (h𝔫 : IsLocalRing.maximalIdeal R ≤ 𝔫.comap (algebraMap R E))
      (_ : ∀ e : E, ∃ r : R, e - algebraMap R E r ∈ 𝔫)
      (τ : Spec (CommRingCat.of E) ⟶ U),
      τ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R E)) ∧
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔫)) ≫ τ =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap 𝔫 (algebraMap R E) h𝔫)) ≫ x := by sorry
