-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp
-- name    : AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_specInt_pullback_forget_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/9962799a-6cc9-5f7f-84ad-fa3b31893463
-- title:
--   Base change of a big fppf sheaf is a small-site sheaf
-- statement:
--   Let $T$ be a scheme (in the bottom universe) and let $\iota : T \to \operatorname{Spec}\mathbf{Z}$ be a morphism of schemes, where $\operatorname{Spec}\mathbf{Z}$ is `specInt`, the spectrum of the ring $\mathbf{Z}$. Let $X$ be a sheaf of abelian groups on the big fppf site of all schemes, that is, on `Scheme.fppfTopology` with values in `Ab`. Consider the small fppf site of $\operatorname{Spec}\mathbf{Z}$: its objects form `specInt.Fppf`, the category of schemes $U$ over $\operatorname{Spec}\mathbf{Z}$ whose structure morphism is flat and locally of finite presentation (the property `fppfProperty`, the infimum of `Flat` and `LocallyOfFinitePresentation`), with arbitrary morphisms over $\operatorname{Spec}\mathbf{Z}$ between them, equipped with the topology `smallFppfTopology specInt` induced by `fppfProperty`. The assertion is that the presheaf on this site obtained by sending such a $U$ to the abelian group $X(U \times_{\operatorname{Spec}\mathbf{Z}} T)$ — formally, the composite of the opposite of the functor `Scheme.Fppf.forget specInt` followed by base change `Over.pullback ι` followed by `Over.forget T` with the underlying presheaf of $X$ — satisfies the sheaf condition for `smallFppfTopology specInt`.
--
--   This is the standard compatibility of fppf sheaves with base change, in the form needed to restrict a big-site abelian sheaf to the small fppf site of $\operatorname{Spec}\mathbf{Z}$ after fibre product with an arbitrary $\mathbf{Z}$-scheme $T$ (for instance a thickening of a fibre); taking $T = \operatorname{Spec}\mathbf{Z}$ and $\iota$ the identity recovers the restriction of $X$ itself. It is used in the construction of the short exact sequence and divisibility statement for fppf cohomology in degree zero recorded by [`AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff`](thm.html#AlgebraicGeometry.exists_shortExact_natCard_fppfCohomology_zero_dvd_of_injective_of_range_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_isSheaf_smallFppfTopology_specInt_pullback_forget_comp.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.isSheaf_smallFppfTopology_specInt_pullback_forget_comp
    {T : Scheme.{0}} (ι : T ⟶ specInt)
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1}) :
    Presheaf.IsSheaf (smallFppfTopology specInt)
      ((Scheme.Fppf.forget specInt ⋙ Over.pullback ι ⋙ Over.forget T).op ⋙ X.obj) := by sorry
