-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
-- name    : AlgebraicGeometry.RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3ea54b8f-3367-5341-9824-d6b901f4aa65
-- title:
--   Theta bundles commute with base change along κ
-- statement:
--   Let $R$ be a commutative ring and let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes that is separated and smooth of relative dimension $1$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\varepsilon_1 \colon \operatorname{Spec} R \to C$ with $\varepsilon_1$ followed by $c$ equal to the identity. Let $R'$ be an $R$-algebra, write $\operatorname{Spec} R' \to \operatorname{Spec} R$ for the induced map and $C_{R'} = C \times_R \operatorname{Spec} R' \to \operatorname{Spec} R'$ (`baseChange`) for the base-changed family, equipped with the section `sectionBaseChange` obtained from $\varepsilon$ by the universal property of the fibre product. Let $t' \colon T \to \operatorname{Spec} R'$ be a scheme over $R'$ and let $M$ be a rigidified line bundle for $(C_{R'}, \varepsilon_{R'})$ over $t'$: a module $M.L$ on $C_{R'} \times_{R'} T$ which is locally isomorphic to the structure sheaf and whose pullback along the rigidifying section $T \to C_{R'} \times_{R'} T$ is isomorphic to the unit module on $T$. Then for all natural numbers $r$ and $n$ there exists an isomorphism of $\mathcal{O}_T$-modules between the theta bundle of $M$ for $(C_{R'}, \varepsilon_{R'})$ over $t'$ and the theta bundle, for $(C,\varepsilon)$ over the composite $T \to \operatorname{Spec} R' \to \operatorname{Spec} R$, of the rigidified line bundle `BaseChange.toR` obtained by pulling $M.L$ back along the inverse of the canonical isomorphism $\kappa \colon C_{R'} \times_{R'} T \xrightarrow{\sim} C \times_R T$. Here the theta bundle of a rigidified line bundle $N$ is the internal-hom dual of the $n$-th exterior power of the pushforward along the second projection of $N.L$ tensored with the inverse module of the $r$-th power of the ideal of the rigidifying section. The assertion is the non-emptiness of the type of such isomorphisms, not the choice of a particular one.
--
--   This is the compatibility of the theta bundle $\Theta_{r,n}$ of a pointed family of curves with extension of the base ring: forming $\Theta_{r,n}$ after base change to $R'$ gives the same $\mathcal{O}_T$-module as forming it over $R$ for the line bundle transported along the canonical identification $C_{R'} \times_{R'} T \cong C \times_R T$. It is used in the comparison of theta bundles under pullback, `nonempty_pullback_fst_thetaBundle_iso_baseChange`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_baseChange_iso_thetaBundle_toR.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange

theorem AlgebraicGeometry.RelPicard.nonempty_thetaBundle_baseChange_iso_thetaBundle_toR
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R'] {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') (r n : ℕ) :
    Nonempty (thetaBundle (baseChange R c R') (sectionBaseChange R' ε) t' M r n ≅
      thetaBundle c ε (t' ≫ specMap R R') (BaseChange.toR c ε R' M) r n) := by sorry
