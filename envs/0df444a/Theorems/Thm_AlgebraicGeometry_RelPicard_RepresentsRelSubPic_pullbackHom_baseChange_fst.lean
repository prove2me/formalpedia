-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_baseChange_fst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/a24f7c88-ba76-5374-a3e5-10e7b511d05f
-- title:
--   Base-change compatibility of the classifying morphism of f^*
-- statement:
--   Let $R$ be a commutative ring, let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $R$ equipped with sections $\varepsilon, \varepsilon'$ (morphisms $\operatorname{Spec} R \to C$, resp. $\to C'$, whose composite with the structure morphism is the identity), and let $f : C' \to C$ satisfy $f \circ c' {=}$ — in diagrammatic form $f \mathbin{\text{followed by}} c = c'$ — and $\varepsilon'$ followed by $f$ equal to $\varepsilon$. Let $D$, $D'$ be designations of relative $\mathrm{Pic}^0$ for $c$, $c'$ (a scheme with a structure morphism to $\operatorname{Spec} R$ and a zero section of it), and let $h$, $h'$ assert that $D$, $D'$ represent the subfunctor of rigidified line bundles cut out by `algEquivZeroCut`, i.e. the condition that for every algebraically closed field $k$ and every $k$-point of the base the restriction to the corresponding fibre is algebraically equivalent to zero: each carries a Poincaré bundle on its base satisfying the condition, together with the universal property that any rigidified line bundle over a base $T$ satisfying the condition is the pullback of the Poincaré bundle along a unique morphism of $R$-schemes $T \to D.\mathtt{toBase}$, and a trivialisation along the zero section. Let $R'$ be an $R$-algebra. Assume further that the base-changed designations $D \times_R R'$ and $D' \times_R R'$ (whose underlying schemes are the fibre products $D.\mathtt{P} \times_{\operatorname{Spec} R} \operatorname{Spec} R'$, resp. for $D'$) represent the corresponding subfunctors for $c \times_R R'$ and $c' \times_R R'$ with the base-changed sections, witnessed by $h_{R'}$ and $h'_{R'}$, and that the Poincaré bundles of $h_{R'}$ and $h'_{R'}$ are isomorphic to the transports along `BaseChange.ofR` of the pullbacks of the Poincaré bundles of $h$ and $h'$ along the first projections $D.\mathtt{P} \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to D.\mathtt{P}$, resp. for $D'$. Assume finally that the base-changed morphism $f \times_R R' = \mathtt{curveChange}\,f$ is compatible with the structure morphisms to $\operatorname{Spec} R'$ and carries the base-changed section of $\varepsilon'$ to that of $\varepsilon$. The conclusion is that the underlying scheme morphism of the classifying morphism $\mathtt{pullbackHom}$ attached to $f \times_R R'$ and to $h_{R'}, h'_{R'}$, followed by the projection $D'.\mathtt{P} \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to D'.\mathtt{P}$, equals the projection $D.\mathtt{P} \times_{\operatorname{Spec} R} \operatorname{Spec} R' \to D.\mathtt{P}$ followed by the underlying scheme morphism of $\mathtt{pullbackHom}$ attached to $f$ and to $h, h'$.
--
--   This is the statement that the morphism of relative $\mathrm{Pic}^0$ schemes induced by a morphism of pointed curves commutes with base change along $R \to R'$, recorded on underlying scheme morphisms composed with the first projection of the fibre product, which pins down the morphism of $R'$-schemes. It is used in the comparison of Néron-model points of $J_0$ with the Jacobian of a modular curve at a prime, where a classifying morphism must be transported through a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_baseChange_fst
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (hR' : RepresentsRelSubPic (baseChange R c' R') (sectionBaseChange R' ε')
      (algEquivZeroCut (baseChange R c' R') (sectionBaseChange R' ε')) (D'.baseChange R'))
    (hPR' : Nonempty (hR'.poincare.L ≅ (BaseChange.ofR c' ε' R'
      (h'.poincare.pullbackAlong ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩)).L))
    (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') = (sectionBaseChange R' ε).1) :
    (RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR').1 ≫
        pullback.fst D'.toBase (specMap R R') =
      pullback.fst D.toBase (specMap R R') ≫ (RepresentsRelSubPic.pullbackHom f hf hε h h').1 := by sorry
