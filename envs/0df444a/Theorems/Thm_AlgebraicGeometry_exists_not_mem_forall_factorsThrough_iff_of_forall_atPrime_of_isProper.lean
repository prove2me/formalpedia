-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
-- name    : AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/aa448c8a-0aa1-5d07-bdc4-dbe0916b5deb
-- title:
--   Spreading out agreement of two closed subschemes of a proper scheme
-- statement:
--   Let $S$ be a noetherian commutative ring, let $A$ be a scheme and let $f \colon A \to \operatorname{Spec} S$ be a proper morphism; let $\iota_1 \colon Z_1 \to A$ and $\iota_2 \colon Z_2 \to A$ be closed immersions, and let $\mathfrak p$ be a prime of $S$. The hypothesis is that $Z_1$ and $Z_2$ have the same affine points over the local ring $S_{\mathfrak p}$, in the following sense: for every commutative ring $R$ and every morphism $\psi \colon \operatorname{Spec} R \to A$ such that $\psi$ followed by $f$ factors through $\operatorname{Spec} S_{\mathfrak p} \to \operatorname{Spec} S$ (that is, there exists $t \colon \operatorname{Spec} R \to \operatorname{Spec} S_{\mathfrak p}$ with $t$ followed by $\operatorname{Spec}$ of the localisation map $S \to S_{\mathfrak p}$ equal to $\psi$ followed by $f$), the morphism $\psi$ factors through $\iota_1$ if and only if it factors through $\iota_2$. The conclusion asserts the existence of an element $g \in S$ with $g \notin \mathfrak p$ such that the same equivalence holds over the localisation $S_g$: for every commutative ring $R$ and every $\psi \colon \operatorname{Spec} R \to A$ whose composite with $f$ factors through $\operatorname{Spec} S_g \to \operatorname{Spec} S$, the morphism $\psi$ factors through $\iota_1$ if and only if it factors through $\iota_2$. Both the hypothesis and the conclusion quantify over affine test schemes only.
--
--   This is a spreading-out statement: agreement of two closed subschemes of a proper $S$-scheme, tested on affine points, propagates from the local base $\operatorname{Spec} S_{\mathfrak p}$ to a basic open neighbourhood $\operatorname{Spec} S_g$ of $\mathfrak p$; properness enters through the closedness of the image of the support of the relevant coherent sheaves. It is used in the study of good reduction of Jacobians, to pass from conditions on kernels of torsion subschemes over a local base to conditions over a basic open subset.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) [IsProper f]
    {Z₁ Z₂ : Scheme.{0}} (ι₁ : Z₁ ⟶ A) (ι₂ : Z₂ ⟶ A) [IsClosedImmersion ι₁] [IsClosedImmersion ι₂]
    (𝔭 : PrimeSpectrum S)
    (h : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ))) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧ ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.Away g)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ Z₁, ψ₁ ≫ ι₁ = ψ) ↔ (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Z₂, ψ₂ ≫ ι₂ = ψ)) := by sorry
