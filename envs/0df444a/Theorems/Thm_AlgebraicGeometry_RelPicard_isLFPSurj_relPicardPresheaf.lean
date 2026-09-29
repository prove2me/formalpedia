-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf
-- name    : AlgebraicGeometry.RelPicard.isLFPSurj_relPicardPresheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/5b3a2625-c412-509e-85ce-ba36c59cc7d5
-- title:
--   Surjectivity along affine limits for the rigidified relative Picard presheaf
-- statement:
--   Let $R$ be a commutative ring and $C$ a scheme equipped with a two-chart affine open cover $\mathcal V$, i.e. two opens $U_0, U_1 \subseteq C$, both affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Let $c \colon C \to \operatorname{Spec} R$ be a morphism and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. The assertion is `AffineLimit.IsLFPSurj` for the presheaf `relPicardPresheaf c ε` on $(\mathrm{Over}\ \operatorname{Spec} R)^{\mathrm{op}}$, whose value at an $R$-scheme $t \colon T \to \operatorname{Spec} R$ is the set of classes, for the setoid `RigidifiedLineBundle.setoid`, of triples consisting of a module $L$ on $C \times_{\operatorname{Spec} R} T$, a proof that $L$ is invertible, and a (nonempty family of) trivialisation(s) of the pullback of $L$ along the rigidifying section determined by $\varepsilon$, with functoriality given by pullback. Unfolded, the conclusion says: for every $R$-algebra $A$ and every class $x$ over $\operatorname{Spec} A$ (taken with its canonical structure morphism to $\operatorname{Spec} R$) there are a finitely generated $R$-subalgebra $A_0 \subseteq A$ and a class $x_0$ over $\operatorname{Spec} A_0$ whose pullback along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ equals $x$.
--
--   This is the surjectivity half of the statement that the rigidified relative Picard functor of $c \colon C \to \operatorname{Spec} R$ is locally of finite presentation, in the form of commuting with filtered unions of $R$-subalgebras, proved here under the hypothesis that $C$ admits a cover by two affine opens with affine intersection. It is used in the corresponding finite-presentation statements for the subpresheaves of classes cut out by the vanishing of an algebra-equivalence condition, `isLFPSurj_relSubPicPresheaf_algEquivZeroCut` and its open-locus variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relPicardPresheaf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isLFPSurj_relPicardPresheaf
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPSurj (relPicardPresheaf c ε) := by sorry
