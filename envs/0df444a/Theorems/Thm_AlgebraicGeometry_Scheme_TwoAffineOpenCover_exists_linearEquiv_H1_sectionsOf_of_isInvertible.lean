-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_H1_sectionsOf_of_isInvertible
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_H1_sectionsOf_of_isInvertible
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-13T17:37:46.278439+00:00
-- url     : https://prove2.me/theorems/73ba4761-179e-433f-8e3e-1d189df1d701
-- title:
--   Degree-one Cech cohomology of a line bundle is independent of a two-affine cover
-- statement:
--   Let $R$ be a commutative ring, let $c:X\to\operatorname{Spec}R$ be a scheme over $R$, and let $M$ be an invertible sheaf on $X$. Suppose
--
--   $$\mathcal U=\{U_0,U_1\},\qquad \mathcal V=\{V_0,V_1\}$$
--
--   are two open covers of $X$, with each chart and each intersection $U_0\cap U_1$ and $V_0\cap V_1$ affine. There is an $R$-linear isomorphism
--
--   $$\check H^1(\mathcal U,M)\simeq\check H^1(\mathcal V,M).$$
--
--   Thus degree-one Cech cohomology of an invertible sheaf is independent of the chosen two-affine cover. Neither cover is required to refine the other. No properness, smoothness, dimension, or field hypothesis is imposed. This comparison permits independently chosen source charts in cohomology calculations for affine morphisms.
--
--   **Formalization Note.** Each degree-one module is the cokernel of the difference of the two restriction maps. Its $R$-module structure is induced by $c$. The formal conclusion asks for existence of a linear equivalence between these concrete cokernels.
-- source:
--   Consequence of Stacks Project, Lemma 30.2.6, Tag 01XD (https://stacks.math.columbia.edu/tag/01XD), applied to each of the two covers and to the quasi-coherent invertible sheaf M. The source identifies affine-cover Cech cohomology with sheaf cohomology as modules over global functions. Compose the two comparisons in degree one and restrict scalars along R -> Gamma(X,O_X). For a two-open cover, the normalized degree-one Cech module is the cokernel of the difference of restrictions. The covers explicitly include affine intersections, so no additional separatedness assumption is needed. This states cover independence, not a literal transcription of the source.

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_linearEquiv_H1_sectionsOf_of_isInvertible
    (R : Type u) [CommRing R] {X : Scheme.{u}}
    (c : X ⟶ Spec (.of R)) (𝒰 𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Nonempty ((𝒰.sectionsOf c M).H1 ≃ₗ[R] (𝒱.sectionsOf c M).H1) := by
  sorry
