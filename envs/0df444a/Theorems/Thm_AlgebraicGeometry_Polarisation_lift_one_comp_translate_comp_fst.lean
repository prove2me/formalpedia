-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst
-- name    : AlgebraicGeometry.Polarisation.lift_one_comp_translate_comp_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/0bc76072-ccfc-5fef-977f-13025016f5f0
-- title:
--   Translation at the unit section recovers the point
-- statement:
--   Let $S$ be a commutative ring, let $A$ be a scheme, let $f : A \to \operatorname{Spec} S$ be a morphism, and let $L$ be a relative group law on $f$ over $S$: that is, for every scheme $T$ and every $t : T \to \operatorname{Spec} S$ a multiplication, a unit and an inversion on the set $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$ of $T$-points of $A$ over $t$, subject to associativity, both unit laws, left inverses, and naturality of the multiplication under precomposition with any $\psi : T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$. Let $x$ be a point of $A$ over the identity of $\operatorname{Spec} S$, i.e. a morphism $x.1 : \operatorname{Spec} S \to A$ with $x.1$ followed by $f$ the identity. Since the unit point $L.\mathrm{one}$ at the identity likewise satisfies this condition, the pair consisting of its underlying morphism and the identity of $\operatorname{Spec} S$ induces a morphism $\sigma : \operatorname{Spec} S \to A \times_{\operatorname{Spec} S} \operatorname{Spec} S$ into the fibre product of $f$ along the identity. The assertion is that $\sigma$, followed by the translation endomorphism $\mathrm{translate}\, f\, L$ by $x$ of that fibre product (the morphism whose first component is the product of the tautological point $\mathrm{pr}_A$ with the pullback of $x$, and whose second component is $\mathrm{pr}_{\operatorname{Spec} S}$), followed by the first projection, equals $x.1$.
--
--   This is the statement that translation by a point $x$, evaluated at the zero section, returns $x$; here it is phrased for the trivial base change of $f$ along the identity of $\operatorname{Spec} S$. It is used in the analysis of when a translation can match a prescribed comparison of framings, where composing with the zero section pins down the translating point and so turns an existential statement over points into a closed condition on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_lift_one_comp_translate_comp_fst.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

theorem AlgebraicGeometry.Polarisation.lift_one_comp_translate_comp_fst
    {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) :
    pullback.lift (L.one (𝟙 (Spec (CommRingCat.of S)))).1 (𝟙 (Spec (CommRingCat.of S))) (by rw [(L.one _).2, Category.comp_id]) ≫
        Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x ≫ pullback.fst f (𝟙 (Spec (CommRingCat.of S))) = x.1 := by sorry
