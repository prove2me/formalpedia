-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
-- name    : AlgebraicGeometry.RelPicard.exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c3aebddd-9ec8-50ca-b8b4-1a549b566b08
-- title:
--   Four structural inputs for relative Picard charts
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c\colon C\to\operatorname{Spec}R$ a separated morphism, and let $\varepsilon$ be a morphism $\operatorname{Spec}R\to C$ with $\varepsilon\circ{}$ — in diagrammatic order, $\varepsilon$ followed by $c$ — equal to the identity. Let $U\subseteq C$ be an open subscheme such that the inclusion followed by $c$ is smooth of relative dimension $1$, with $\operatorname{range}\varepsilon\subseteq U$, and assume the covering hypothesis `hcov`: for every affine open $V$ of $\operatorname{Spec}R$ and every finite set $F$ of points of $U$ all mapping into $V$, there is an affine open $W$ of the scheme $U$ contained in the preimage of $V$ and containing $F$. Let $r,g,e$ be natural numbers. Let $y\colon Y\to\operatorname{Spec}R$ and let $D_{\mathrm{univ}}$ be a relative effective Cartier divisor of degree $g$ for $c$ over $y$, that is, an ideal sheaf datum $I$ on $C\times_{\operatorname{Spec}R}Y$ whose closed subscheme is finite, flat and locally of finite presentation over $Y$ with all fibre ranks equal to $g$, whose support lies in the preimage of $U$ under the first projection, and which is universal among such data supported in $U$: for every $g'\colon T\to\operatorname{Spec}R$ and every degree-$g$ relative effective Cartier divisor $D$ over $g'$ supported in $U$ there is a unique $\varphi\colon T\to Y$ with $\varphi$ followed by $y$ equal to $g'$ whose associated comap carries $D_{\mathrm{univ}}$'s ideal to that of $D$. Let $(X_i)_{i\in\iota}$ be schemes, each equipped with a map $f_i$ from the (lifted) representable presheaf of $X_i$ to the total presheaf over $\operatorname{Spec}R$ of the subfunctor of the relative Picard presheaf of $(c,\varepsilon)$ cut out by fibrewise algebraic equivalence to zero, and assume each $X_i$ admits an open immersion $j\colon X_i\to Y$ with $j$ followed by $y$ equal to the structure morphism underlying $f_i$. Finally let $D_{\gamma,i}$, $i\in\iota$, be degree-$e$ relative effective Cartier divisors for $c$ over the identity of $\operatorname{Spec}R$, each supported in $U$. Then four assertions hold simultaneously: (1) for every $i$ and every finite subset $F$ of $X_i$ there is an affine open of $X_i$ containing $F$; (2) for every $t\colon T\to\operatorname{Spec}R$ the ideal sheaf datum `sectionIdeal c ε t`, the kernel of the rigidifying section $T\to C\times_{\operatorname{Spec}R}T$, is invertible, i.e. locally generated on suitable affine basic opens by a single non-zero-divisor; (3) for every $i$ and every $t\colon T\to\operatorname{Spec}R$ the ideal of the pullback of $D_{\gamma,i}$ along $t$ is invertible in the same sense; and (4) for all $t\colon T\to\operatorname{Spec}R$, $t'\colon T'\to\operatorname{Spec}R$ and every morphism $\psi\colon T'\to T$ over $\operatorname{Spec}R$, the pullback along the induced base-change morphism of the $r$-th section twist $(\,\mathcal I^{r}\,)^{\vee}$ over $T$ is isomorphic to the corresponding twist over $T'$.
--
--   The four conclusions are exactly the structural inputs (common affine neighbourhoods of finite sets in the charts, invertibility of the section ideal and of the ideals of the auxiliary divisors, and base-change compatibility of the section twists) required by the orbit argument used in the representability of the fibrewise-algebraically-trivial part of the relative Picard functor. It is invoked in the construction of such representing schemes after base change away from a prime, both in the smooth-curve-degeneration and the line-degeneration settings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_isAffineOpen_and_isInvertible_sectionIdeal_and_isInvertible_pullbackAlong_and_sectionTwist_of_isOpenImmersion_of_supportedIn
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (hcov : ∀ (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset ↥U),
      (∀ x ∈ F, (U.ι ≫ c) x ∈ (V : (Spec (CommRingCat.of R)).Opens)) →
      ∃ W : (↑U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ (U.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧
        ∀ x ∈ F, x ∈ W)
    (r g e : ℕ)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (Duniv : RelEffCartierDiv c g y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g' : T ⟶ Spec (CommRingCat.of R)) (D : RelEffCartierDiv c g g'), D.SupportedIn U →
        ∃! φ : {φ : T ⟶ Y // φ ≫ y = g'}, PullsBackOver Duniv φ.1 φ.2 D)

    {ι : Type u} (X : ι → Scheme.{u})
    (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal)
    (hj : ∀ i, ∃ j : X i ⟶ Y, IsOpenImmersion j ∧ j ≫ y = (uliftYonedaEquiv (f i)).1)

    (Dγ : ι → RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : ∀ i, (Dγ i).SupportedIn U) :
    (∀ (i : ι) (F : Finset (X i)), ∃ U : (X i).Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U) ∧
    (∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)), (sectionIdeal c ε t).IsInvertible) ∧
    (∀ (i : ι) ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)),
      ((Dγ i).pullbackAlong t (Category.comp_id t)).I.IsInvertible) ∧
    (∀ ⦃T T' : Scheme.{u}⦄ {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t),
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (sectionTwist c ε t r) ≅ sectionTwist c ε t' r)) := by sorry
