-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/3e231935-e927-5fce-b799-07075908c210
-- title:
--   Transport of two-chart Čech cohomology along a scheme isomorphism
-- statement:
--   Let $R$ be a commutative ring, let $X$ and $X'$ be schemes equipped with morphisms $x : X \to \operatorname{Spec} R$ and $x' : X' \to \operatorname{Spec} R$, and let $\varphi : X \cong X'$ be an isomorphism of schemes compatible with these structure morphisms, in the sense that $\varphi$ followed by $x'$ equals $x$. Let $\mathcal V'$ be a `TwoAffineOpenCover` of $X'$, that is, a pair of opens $U'_0, U'_1 \subseteq X'$ with $U'_0$, $U'_1$ and $U'_0 \cap U'_1$ all affine and $U'_0 \cup U'_1 = X'$. Let $M'$ be an $\mathcal O_{X'}$-module, $M$ an $\mathcal O_X$-module, and $e$ an isomorphism of $\mathcal O_X$-modules from $M$ to the pullback of $M'$ along $\varphi$. Then there exists a `TwoAffineOpenCover` $\mathcal V$ of $X$ whose two opens are exactly the preimages $\varphi^{-1}U'_0$ and $\varphi^{-1}U'_1$, such that the associated two-term Čech data are cohomologically identified over $R$: writing $\mathcal V.\mathrm{sectionsOf}$ for the complex with terms $\Gamma(M,\mathcal V.U_0) \times \Gamma(M,\mathcal V.U_1) \to \Gamma(M,\mathcal V.U_0 \cap \mathcal V.U_1)$, $(m_0,m_1) \mapsto m_1|_{} - m_0|_{}$, with $R$-module structures induced by $x$, its kernel $H^0$ and its cokernel $H^1$ admit $R$-linear isomorphisms with the corresponding kernel and cokernel for $\mathcal V'$, $x'$ and $M'$. The two cohomological conclusions are asserted as `Nonempty` statements, so no particular comparison map is named.
--
--   This is transport of structure for the two-chart Čech description of cohomology used throughout the library, where the complex is attached to a named pair of affine opens and a named module rather than to a sheaf alone. It lets one replace a scheme–cover–module datum by an isomorphic one, for instance when passing between different presentations of the same fibre of a family, and is invoked by a large number of downstream computations of $H^0$ and $H^1$ for curves and line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    {R : Type u} [CommRing R] {X X' : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of R)) (x' : X' ⟶ Spec (CommRingCat.of R))
    (φ : X ≅ X') (hφ : φ.hom ≫ x' = x) (𝒱' : X'.TwoAffineOpenCover) (M' : X'.Modules) (M : X.Modules)
    (e : M ≅ (Scheme.Modules.pullback φ.hom).obj M') :
    ∃ 𝒱 : X.TwoAffineOpenCover, 𝒱.U0 = φ.hom ⁻¹ᵁ 𝒱'.U0 ∧ 𝒱.U1 = φ.hom ⁻¹ᵁ 𝒱'.U1 ∧
      Nonempty ((𝒱.sectionsOf x M).H0 ≃ₗ[R] (𝒱'.sectionsOf x' M').H0) ∧
      Nonempty ((𝒱.sectionsOf x M).H1 ≃ₗ[R] (𝒱'.sectionsOf x' M').H1) := by sorry
