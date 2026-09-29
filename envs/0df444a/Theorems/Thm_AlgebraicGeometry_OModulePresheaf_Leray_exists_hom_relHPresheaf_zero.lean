-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/3d9b2dcb-0a6d-5538-a236-34e5102badde
-- title:
--   Degree-zero relative Čech presheaf is p_*mathcal O_{V'}
-- statement:
--   Let $R$ be a commutative ring, let $V'$ and $Z$ be schemes, let $p \colon V' \to Z$ and $\pi_Z \colon Z \to \operatorname{Spec} R$ be morphisms of schemes, and let $K'$ be an ordered affine cover of $V'$, that is, a finite linearly ordered index set together with affine opens $K'_i \subseteq V'$ whose supremum is $\top$. The assertion is that there is a morphism $\varphi$ of $\mathcal O$-module presheaves over $\pi_Z$ — a family of $R$-linear maps $\varphi_U$, one for each open $U \subseteq Z$, each compatible with the $\Gamma(Z,U)$-action and with the restriction maps — from `relHPresheaf p πZ K' 0`, whose value at $U$ is the quotient of $\ker\bigl(\mathrm{d}^0_U\bigr)$ by the submodule `relAltHB p πZ K' U 0`, to `pullOpen p πZ ⊤`, whose value at $U$ is $\Gamma(V', \top \sqcap p^{-1}U)$ with $\Gamma(Z,U)$ acting through $p^{\sharp}$; here $\mathrm{d}^0_U$ is the alternating Čech differential $\prod_i \Gamma(V', K'_i \sqcap p^{-1}U) \to \prod_{i<j} \Gamma(V', K'_i \sqcap K'_j \sqcap p^{-1}U)$ given by the alternating sum of restrictions along the faces. Moreover $\varphi_U$ is bijective for every $U$, and for every $x \in \ker(\mathrm{d}^0_U)$ the augmentation `relAug p πZ K' U`, which restricts a section on $\top \sqcap p^{-1}U$ to each $K'_i \sqcap p^{-1}U$, sends $\varphi_U$ of the class of $x$ back to the tuple $x$.
--
--   This is the sheaf-condition (equalizer) identification of the degree-zero relative Čech cohomology presheaf of $\mathcal O_{V'}$ along the cover $K'$ with the direct image $p_*\mathcal O_{V'}$, in the form of an isomorphism of presheaves of $\mathcal O_Z$-modules splitting the augmentation on representatives. It feeds the construction of the short exact sequence used in [`AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES) and the descent of differentials in [`AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.exists_hom_relHPresheaf_zero
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K' : V'.OrderedAffineCover) :
    ∃ φ : OModulePresheaf.Hom (OModulePresheaf.Leray.relHPresheaf p πZ K' 0)
        (OModulePresheaf.Leray.pullOpen p πZ (⊤ : V'.Opens)),
      (∀ U : Z.Opens, Function.Bijective (φ.app U)) ∧
      ∀ (U : Z.Opens) (x : LinearMap.ker (OModulePresheaf.Leray.relAltd p πZ K' U 0)),
        OModulePresheaf.Leray.relAug p πZ K' U (φ.app U (Submodule.Quotient.mk x)) = x.1 := by sorry
