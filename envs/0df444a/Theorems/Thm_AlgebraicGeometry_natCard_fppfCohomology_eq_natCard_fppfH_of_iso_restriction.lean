-- Prove2me | Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
-- name    : AlgebraicGeometry.natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/ddee6398-d7ca-5b77-8042-0fa7e200769f
-- title:
--   Small- and big-fppf H⁰ and H¹ over Specℤ agree
-- statement:
--   Let $X$ be a sheaf of abelian groups (in `Ab.{1}`) on the big fppf site, i.e. on the category of schemes in universe $0$ equipped with `Scheme.fppfTopology`, and let $L$ be a sheaf of abelian groups on the small fppf site of $\operatorname{Spec}\mathbb{Z}$: the site whose underlying category `specInt.Fppf` consists of the objects of the over-category of $\operatorname{Spec}\mathbb{Z}$ whose structure morphism is flat and locally of finite presentation (morphisms being all morphisms over $\operatorname{Spec}\mathbb{Z}$), with the topology `smallFppfTopology` induced by that morphism property. Assume given an isomorphism $e$ of presheaves between the underlying presheaf of $L$ and the restriction of the underlying presheaf of $X$ along the opposite of the forgetful functor `specInt.Fppf` $\to$ `Over specInt` $\to$ `Scheme`. Then the natural-number cardinalities of the small-site sheaf cohomology groups $H^n(L)$ and of the big-site groups $H^n(X)$ agree for $n=0$ and $n=1$; here both cohomologies are the sheaf cohomology `F.H n`, and `Nat.card` records the value $0$ when a group is infinite.
--
--   This is the comparison of small-site and big-site flat cohomology in degrees $\le 1$ over the terminal base $\operatorname{Spec}\mathbb{Z}$, for a pair of sheaves coupled by restriction along the inclusion of the flat, locally finitely presented test objects. It is used in the finiteness and counting estimates for flat cohomology of the Néron model of $J_0$, where the two presentations of flat cohomology must be interchanged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.natCard_fppfCohomology_eq_natCard_fppfH_of_iso_restriction
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 0) = Nat.card (FppfCohomologyLES.FppfH X 0) ∧
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) := by sorry
