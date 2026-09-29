-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away
-- name    : AlgebraicGeometry.Scheme.existsUnique_section_of_forall_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/4247a5b5-2f74-5497-b0be-cd3df3e222ad
-- title:
--   Gluing sections of a scheme over a principal open cover of Spec S
-- statement:
--   Let $S$ be a commutative ring, $k$ a natural number and $r : \mathrm{Fin}\,k \to S$ a family of elements whose span is the unit ideal, and let $B_i$ ($i \in \mathrm{Fin}\,k$) be commutative $S$-algebras such that $B_i$ is a localisation of $S$ away from $r_i$. Let $A$ be a scheme, $f : A \to \operatorname{Spec} S$ a morphism, and for each $i$ let $\sigma_i : \operatorname{Spec} B_i \to A$ be a morphism over $\operatorname{Spec} S$, i.e. $\sigma_i$ followed by $f$ equals $\operatorname{Spec}$ of the structure map $S \to B_i$. Assume the following agreement on overlaps: for all $i, j$, every commutative $S$-algebra $C$ which is a localisation of $S$ away from $r_i r_j$, and all $S$-algebra homomorphisms $\rho_1 : B_i \to C$ and $\rho_2 : B_j \to C$, the morphism $\operatorname{Spec} \rho_1$ followed by $\sigma_i$ equals $\operatorname{Spec} \rho_2$ followed by $\sigma_j$. Then there exists a morphism $\sigma_0 : \operatorname{Spec} S \to A$ such that $\sigma_0$ followed by $f$ is the identity of $\operatorname{Spec} S$, such that for every $i$ the morphism $\operatorname{Spec}(S \to B_i)$ followed by $\sigma_0$ equals $\sigma_i$, and such that any $\sigma_1 : \operatorname{Spec} S \to A$ with this last restriction property for all $i$ equals $\sigma_0$. Thus uniqueness is asserted among all morphisms restricting to the $\sigma_i$, without assuming that they are sections of $f$.
--
--   This is the standard descent statement that sections of a scheme over the members of a principal (distinguished) affine open cover of $\operatorname{Spec} S$ which agree on pairwise overlaps glue to a unique global section, formulated with the overlaps presented as abstract localisations away from the products $r_i r_j$ so that it can be applied without choosing models. It is used in the construction of sections of abelian schemes and of pullback data, in [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_forall_isPullback_of_forall_away_of_isMaximalOrder_of_isUnit_two) and [`AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_forall_isPullback_iso_of_forall_iso_localizationAway_of_three_le_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_section_of_forall_away.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.Scheme.existsUnique_section_of_forall_away
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (B : Fin k → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra S (B i)] [∀ i, IsLocalization.Away (r i) (B i)]
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (σ : ∀ i, Spec (CommRingCat.of (B i)) ⟶ A)
    (hσ : ∀ i, σ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S (B i))))
    (hagree : ∀ (i j : Fin k) (C : Type u) [CommRing C] [Algebra S C] [IsLocalization.Away (r i * r j) C]
      (ρ₁ : B i →ₐ[S] C) (ρ₂ : B j →ₐ[S] C),
      Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ σ i = Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ σ j) :
    ∃ σ₀ : Spec (CommRingCat.of S) ⟶ A, σ₀ ≫ f = 𝟙 _ ∧
      (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₀ = σ i) ∧
      ∀ σ₁ : Spec (CommRingCat.of S) ⟶ A, (∀ i, Spec.map (CommRingCat.ofHom (algebraMap S (B i))) ≫ σ₁ = σ i) → σ₁ = σ₀ := by sorry
