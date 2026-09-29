-- Prove2me | Theorems.Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
-- name    : AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/f350a292-b258-541a-8141-73c09f2ace94
-- title:
--   Equal cardinality of small- and big-fppf H¹ over Specℤ
-- statement:
--   Let $X$ be a sheaf of abelian groups (with values in $\mathrm{Ab}$ one universe up) on the big fppf site of schemes, that is, on `Scheme.{0}` equipped with `Scheme.fppfTopology`, and let $L$ be a sheaf of abelian groups on the small fppf site of `specInt` $= \operatorname{Spec}\mathbb{Z}$: its objects are the $\operatorname{Spec}\mathbb{Z}$-schemes whose structure morphism is flat and locally of finite presentation, with arbitrary morphisms over $\operatorname{Spec}\mathbb{Z}$, and the topology is `smallFppfTopology specInt`, the small Grothendieck topology attached to the morphism property `fppfProperty` $=$ flat $\wedge$ locally of finite presentation. Suppose given an isomorphism $e$ of presheaves of abelian groups on this small site between the underlying presheaf of $L$ and the restriction of the underlying presheaf of $X$ along the functor sending an object of the small fppf site of $\operatorname{Spec}\mathbb{Z}$ to its underlying scheme (the composite of `Scheme.Fppf.forget specInt` with `Over.forget specInt`, opposed). Then the natural-number cardinalities of the first cohomology groups agree: $\mathrm{Nat.card}$ of `fppfCohomology specInt L 1`, i.e. of $L.H^1$ on the small site, equals $\mathrm{Nat.card}$ of [`FppfCohomologyLES.FppfH X 1`](def/AlgebraicGeometry_FppfCohomologyLES.html#L175), i.e. of $X.H^1$ on the big site. Since `Nat.card` vanishes on infinite types, the statement also holds, vacuously, when both groups are infinite.
--
--   This is the comparison of small-site and big-site fppf cohomology in degree one over $\operatorname{Spec}\mathbb{Z}$, in the cardinality form in which it is used downstream. It feeds the finiteness results for fppf $H^1$ of sheaves arising from group schemes of prime order, and a companion statement covering general degrees.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.natCard_fppfCohomology_one_eq_natCard_fppfH_one_of_iso_restriction
    (X : Sheaf Scheme.fppfTopology.{0} Ab.{1})
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : L.obj ≅ (Scheme.Fppf.forget specInt ⋙ Over.forget specInt).op ⋙ X.obj) :
    Nat.card (fppfCohomology specInt L 1) = Nat.card (FppfCohomologyLES.FppfH X 1) := by sorry
