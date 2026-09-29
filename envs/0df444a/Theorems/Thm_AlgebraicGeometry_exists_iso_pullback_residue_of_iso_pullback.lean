-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback
-- name    : AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/646b6a92-4205-522a-9186-10a69b990316
-- title:
--   Closed fibres agree under residually surjective local base change
-- statement:
--   Let $A$ and $A_1$ be local rings (commutative, in a fixed universe) and let $\iota_1 : A_1 \to A$ be a ring homomorphism which is local, i.e. pulls the maximal ideal of $A$ back into that of $A_1$; assume moreover that the composite $A_1 \to A \to \kappa(A)$ of $\iota_1$ with the residue map of $A$ is surjective. Let $X$ and $X_1$ be schemes, let $\mathrm{toBase} : X \to \operatorname{Spec} A$ and $f_1 : X_1 \to \operatorname{Spec} A_1$ be morphisms, and suppose given an isomorphism $e_1 : X \xrightarrow{\ \sim\ } X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} A$, the fibre product being taken along $\operatorname{Spec}(\iota_1)$, such that $e_1$ followed by the second projection to $\operatorname{Spec} A$ is $\mathrm{toBase}$. The assertion is that there exists an isomorphism of schemes
--   $$\rho : X \times_{\operatorname{Spec} A} \operatorname{Spec} \kappa(A) \xrightarrow{\ \sim\ } X_1 \times_{\operatorname{Spec} A_1} \operatorname{Spec} \kappa(A_1),$$
--   the two fibre products being formed along the morphisms induced by the respective residue maps, which is compatible with the projections to $X_1$: the map $\rho$ followed by the first projection of the right-hand pullback agrees with the first projection $X \times_{\operatorname{Spec} A} \operatorname{Spec}\kappa(A) \to X$ followed by $e_1$ followed by the first projection onto $X_1$.
--
--   This is the statement that the closed fibre of a scheme over a local ring may be computed at any residually surjective local subring over which the scheme is obtained by base change — the residue field map $\kappa(A_1) \to \kappa(A)$ being an isomorphism, and fibre products pasting. It is used to transfer properties of special fibres, such as reducedness and the shape of the fibre, between a model over a local ring and a model over a smaller local ring, in [`AlgebraicCurve.SemistableModel.fibre_shapes_of_level`](thm.html#AlgebraicCurve.SemistableModel.fibre_shapes_of_level) and [`AlgebraicCurve.SemistableModel.isReduced_pullback_residue_of_level`](thm.html#AlgebraicCurve.SemistableModel.isReduced_pullback_residue_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_iso_pullback_residue_of_iso_pullback.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_pullback_residue_of_iso_pullback
    {A A₁ : Type u} [CommRing A] [IsLocalRing A] [CommRing A₁] [IsLocalRing A₁]
    (ι₁ : A₁ →+* A) [IsLocalHom ι₁] (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    {X X₁ : Scheme.{u}} (toBase : X ⟶ Spec (CommRingCat.of A)) (f₁ : X₁ ⟶ Spec (CommRingCat.of A₁))
    (e₁ : X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = toBase) :
    ∃ ρ : pullback toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≅
        pullback f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))),
      ρ.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A₁))) =
        pullback.fst toBase (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
          e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁)) := by sorry
