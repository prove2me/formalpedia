-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_finrank_H1_unit_fibre_eq_of_eulerChar_chart
-- name    : AlgebraicGeometry.RelPicard.finrank_H1_unit_fibre_eq_of_eulerChar_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/edd13ac7-b8c7-5c55-bad9-5aa1805de8a2
-- title:
--   Euler characteristic 1 on fibres forces h¹(𝒪)=g
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c\colon C\to\operatorname{Spec}R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a morphism $\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ the identity. Let $g,e,r$ be natural numbers with $g+e=r$, and let $D_\gamma$ be a relative effective Cartier divisor of degree $e$ for $c$ over the identity of $\operatorname{Spec}R$: an ideal sheaf datum $I$ on $\operatorname{pullback} c\,\mathrm{id}$ whose closed immersion followed by the second projection is finite, flat, locally of finite presentation, and of fibre rank $e$ at every point. Write $M$ for the pullback to a geometric fibre of $((\text{the kernel ideal of }\varepsilon)^r)^{\vee}\otimes I$-module, i.e. of `sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule`. Assume that for every algebraically closed field $k$, every $x\colon\operatorname{Spec}k\to\operatorname{Spec}R$ and every cover of the fibre by two affine opens whose union is everything and whose intersection is affine, the two-chart Čech groups of $M$ over $k$ satisfy $\dim_k H^0-\dim_k H^1=1$. Then for any such $k$, $x$ and two-chart cover, $\dim_k H^1$ of the two-chart Čech complex of the tensor unit (the structure sheaf) of the fibre equals $g$.
--
--   This is the normalisation step of a Riemann–Roch bookkeeping on a smooth proper relatively one-dimensional curve: prescribing the Euler characteristic $\chi(\mathcal O(r\varepsilon-D_\gamma))=1$ together with $g+\deg D_\gamma=r$ pins the genus of every geometric fibre, in the two-chart Čech formulation used throughout. It supplies the genus input for the construction of relative effective divisors representing line bundles, and is cited by [`AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1`](thm.html#AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_finrank_H1_unit_fibre_eq_of_eulerChar_chart.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.finrank_H1_unit_fibre_eq_of_eulerChar_chart
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ Dγ.idealModule))).H1 = 1)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
      (𝟙_ (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).Modules)).H1 = g := by sorry
