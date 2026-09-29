-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
-- name    : AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a8de076a-5f97-506c-9c46-4f132ef5e17e
-- title:
--   Flat affine closed subschemes with isomorphic generic fibres
-- statement:
--   Let $R$ be a commutative domain with fraction field $K$ (that is, $K$ is a field, an $R$-algebra, and a fraction ring of $R$), let $Y$ be a scheme and $f : Y \to \operatorname{Spec} R$ a morphism. Let $A_1, A_2$ be commutative $R$-algebras that are flat as $R$-modules, and let $i_1 : \operatorname{Spec} A_1 \to Y$ and $i_2 : \operatorname{Spec} A_2 \to Y$ be closed immersions, assumed compatible with the structure morphisms in the sense that $i_1$ followed by $f$ equals $\operatorname{Spec}$ of the structure map $R \to A_1$, and likewise for $i_2$. Assume given an isomorphism of schemes $e_K : \operatorname{Spec}(K \otimes_R A_1) \xrightarrow{\ \sim\ } \operatorname{Spec}(K \otimes_R A_2)$ such that $e_K$ followed by $\operatorname{Spec}$ of the right inclusion $A_2 \to K \otimes_R A_2$ and then by $i_2$ equals $\operatorname{Spec}$ of the right inclusion $A_1 \to K \otimes_R A_1$ followed by $i_1$. The conclusion is that there exists an isomorphism $e : \operatorname{Spec} A_1 \xrightarrow{\ \sim\ } \operatorname{Spec} A_2$ with $e$ followed by $i_2$ equal to $i_1$; no compatibility of $e$ with $e_K$ is asserted. All schemes live in the zeroth universe.
--
--   This is the statement that a closed subscheme of $Y$ which is affine and flat over the base domain $R$ is determined by its generic fibre, i.e. is the schematic closure of that fibre; it is the uniqueness half of the theory of schematic closures of flat subschemes. It is used to identify, inside a Néron model, the kernel of a Raynaud quotient of the finite part with Grothendieck's toric lift, via the consumer [`ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff`](thm.html#ModularCurve.JHNeronObjectAtP.exists_bialgEquiv_comp_toricLift_eq_of_isClosedImmersion_of_flat_of_forall_mem_toricPts_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
    {R : Type} [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
    [Module.Flat R A₁] [Module.Flat R A₂]
    (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (i₂ : Spec (CommRingCat.of A₂) ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁)))
    (h₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₂)))
    (eK : Spec (CommRingCat.of (K ⊗[R] A₁)) ≅ Spec (CommRingCat.of (K ⊗[R] A₂)))
    (heK : eK.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₂ →+* K ⊗[R] A₂)) ≫ i₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁) :
    ∃ e : Spec (CommRingCat.of A₁) ≅ Spec (CommRingCat.of A₂), e.hom ≫ i₂ = i₁ := by sorry
