-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_le_iff_map_localization_comap_ideal_top_le
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.map_germ_le_iff_map_localization_comap_ideal_top_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8eac5929-3c6f-5b5b-8dbf-1a2ad8a3dce8
-- title:
--   Germ comparison of ideal sheaves via localised chart ideals
-- statement:
--   Let $Y$ be a scheme, let $A$ be a commutative ring (in the same universe), let $\iota : \operatorname{Spec} A \to Y$ be an open immersion of schemes, and let $\mathfrak p$ be a prime ideal of $A$, regarded as the point $\mathfrak p$ of $\operatorname{Spec} A$. Let $I$ and $J$ be ideal sheaf data on $Y$ (that is, quasi-coherent ideal sheaves presented by their ideals $I.\mathrm{ideal}\,U \subseteq \mathcal O_Y(U)$ on affine opens $U$), let $U$ be an affine open of $Y$, and assume that $\iota(\mathfrak p) \in U$. The assertion is an equivalence of two inclusions. On one side, the images of the ideals $I.\mathrm{ideal}\,U$ and $J.\mathrm{ideal}\,U$ under the germ map $\mathcal O_Y(U) \to \mathcal O_{Y,\iota(\mathfrak p)}$ at $\iota(\mathfrak p)$ satisfy the first inclusion. On the other, the images of the chart ideals $(I.\mathrm{comap}\,\iota).\mathrm{ideal}$ and $(J.\mathrm{comap}\,\iota).\mathrm{ideal}$ at the affine open $\top$ of $\operatorname{Spec} A$ — the pullbacks of $I$ and $J$ along $\iota$ evaluated on all of $\operatorname{Spec} A$ — satisfy the corresponding inclusion after transport along the ring map obtained by composing the isomorphism $\Gamma(\operatorname{Spec} A) \cong A$ given by `Scheme.ΓSpecIso` with the localisation map $A \to A_{\mathfrak p}$. The two inclusions hold or fail together.
--
--   This is the standard chart bridge for quasi-coherent ideal sheaves: an open immersion from an affine scheme identifies the stalk of $\mathcal O_Y$ at $\iota(\mathfrak p)$ with $A_{\mathfrak p}$, and the germ of an ideal sheaf with the localisation at $\mathfrak p$ of the ideal it cuts out on the chart $\operatorname{Spec} A$. It is used to convert germ-level inclusions of ideal sheaves into inclusions of explicit ideals in a localised coordinate ring, in the divisor computations for Weierstrass models feeding [`WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod`](thm.html#WeierstrassCurve.DrinfeldGlobal.torsionIdeal_le_basisDivisor_of_nsmul_eq_one_of_nthSeries_eq_mul_prod).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_le_iff_map_localization_comap_ideal_top_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_le_iff_map_localization_comap_ideal_top_le
    {Y : Scheme.{u}} (A : Type u) [CommRing A] (ι : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion ι]
    (𝔭 : Ideal A) [𝔭.IsPrime] (I J : Y.IdealSheafData)
    (U : Y.affineOpens) (hU : ι.base (⟨𝔭, inferInstance⟩ : PrimeSpectrum A) ∈ (U : Y.Opens)) :
    Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (I.ideal U) ≤
        Ideal.map (Y.presheaf.germ (U : Y.Opens) _ hU).hom (J.ideal U) ↔
      Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((I.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) ≤
        Ideal.map ((algebraMap A (Localization.AtPrime 𝔭)).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
          ((J.comap ι).ideal ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩) := by sorry
