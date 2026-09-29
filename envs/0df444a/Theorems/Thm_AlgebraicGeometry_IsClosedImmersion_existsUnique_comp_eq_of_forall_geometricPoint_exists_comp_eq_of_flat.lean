-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat
-- name    : AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/95168d4b-5e9c-5ece-a21d-3c0a84345a0d
-- title:
--   Factoring through a closed immersion via generic geometric points
-- statement:
--   Let $R$ be a commutative ring which is a domain, let $\Omega$ be an algebraically closed field (both in the same universe), and let $\iota \colon R \to \Omega$ be an injective ring homomorphism. Let $X$, $Y$, $Z$ be schemes, let $f \colon X \to \operatorname{Spec} R$ be flat and locally of finite presentation, with $X$ reduced, let $i \colon Z \to Y$ be a closed immersion, and let $\varphi \colon X \to Y$ be an arbitrary morphism. Assume that for every morphism $x \colon \operatorname{Spec}\Omega \to X$ whose composite with $f$ equals $\operatorname{Spec}$ of $\iota$, there exists a morphism $z \colon \operatorname{Spec}\Omega \to Z$ with $z$ followed by $i$ equal to $x$ followed by $\varphi$; that is, every $\Omega$-valued point of $X$ lying over the given geometric point of the generic point of $\operatorname{Spec} R$ is carried by $\varphi$ into $Z$. The conclusion is that there is exactly one morphism $\psi \colon X \to Z$ with $\psi$ followed by $i$ equal to $\varphi$. No separatedness hypothesis on $Y$ is imposed.
--
--   This is the factorisation counterpart of the rigidity principle of EGA IV$_3$ 11.10.9–11.10.10: over a domain, a reduced scheme flat and locally of finite presentation is controlled by the geometric points of its generic fibre. It is used in the construction of the modular curve $X_1$, to descend a morphism to a closed subscheme once the descent is known on geometric points of the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_forall_geometricPoint_exists_comp_eq_of_flat
    {R : Type u} [CommRing R] [IsDomain R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ι : R →+* Ω) (hι : Function.Injective ι)
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [LocallyOfFinitePresentation f]
    [IsReduced X] (i : Z ⟶ Y) [IsClosedImmersion i] (φ : X ⟶ Y)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X, x ≫ f = Spec.map (CommRingCat.ofHom ι) →
      ∃ z : Spec (CommRingCat.of Ω) ⟶ Z, z ≫ i = x ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ i = φ := by sorry
