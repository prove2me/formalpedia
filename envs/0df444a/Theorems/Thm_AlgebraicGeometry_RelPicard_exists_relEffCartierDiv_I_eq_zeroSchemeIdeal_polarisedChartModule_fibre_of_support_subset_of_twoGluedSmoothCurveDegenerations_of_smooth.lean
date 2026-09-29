-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_smooth
-- name    : AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/088e6448-13a1-5272-8c1a-a49e67b7e325
-- title:
--   Degree-g zero divisors of theta-chart sections over smooth fibres
-- statement:
--   Let $R$ be a Noetherian commutative ring, $c : C \to \operatorname{Spec} R$ a proper flat morphism of schemes, $\mathcal{V}$ a two-chart affine open cover of $C$ (two affine opens with affine intersection covering $C$), and $U \subseteq C$ an open such that $U \hookrightarrow C \to \operatorname{Spec} R$ is smooth of relative dimension $1$; let $\varepsilon$ be a section of $c$, and let $g, e, \rho$ be naturals with $g + e = \rho$. Let $E$ and $D_\gamma$ be relative effective Cartier divisors for $c$ over the identity of $\operatorname{Spec} R$ of degrees $\rho$ and $e$ respectively — ideal sheaf data whose closed subscheme is finite, flat and locally of finite presentation over the base with constant fibre rank — each supported in $U$, i.e. with support contained in the preimage of $U$ under the first projection. Assume: (hχ) for every algebraically closed field $k$, every $x : \operatorname{Spec} k \to \operatorname{Spec} R$ and every two-chart affine cover $\mathcal{W}$ of the fibre, the difference of $k$-dimensions of $H^0$ and $H^1$ of the two-term Čech complex of sections of the fibrewise pullback of $E.\mathrm{lineBundle} \otimes D_\gamma.\mathrm{idealModule}$ (the dual of $E$'s ideal module tensored with $D_\gamma$'s ideal module) equals $1$; (hg) in the same situation the $H^1$ of the structure sheaf has dimension $g$; (hgoodU) whenever a geometric fibre $\operatorname{pullback.snd}\,c\,x$ is smooth, the image of the first projection of that fibre lies in $U$; (hgoodirr) such smooth geometric fibres are geometrically irreducible; (hgred) all geometric fibres are reduced. Then for every $T$ with $t : T \to \operatorname{Spec} R$ locally of finite type, every rigidified line bundle $L$ for $(c, \varepsilon)$ over $t$ (an invertible module on $C \times_{\operatorname{Spec} R} T$ trivialised along the rigidifying section) which is fibrewise algebraically equivalent to zero, every algebraically closed field $k$ and $x : \operatorname{Spec} k \to T$ with $\operatorname{pullback.snd}\,c\,(x \circ t)$ smooth, and every nonzero morphism $\sigma$ from the unit module of $C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ to the pullback along $\mathrm{mapOnProdOver}$ of $L.L$ tensored with the line bundle of $E$ and the ideal module of $D_\gamma$ pulled back along $t$, whose zero-scheme ideal has support inside the preimage of $U$: there is a relative effective Cartier divisor $D_x$ for $c$ of degree $g$ over $x \circ t$ whose ideal is exactly the zero-scheme ideal of $\sigma$ and which is supported in $U$.
--
--   This is the smooth-fibre case of the statement that a nonzero section of the theta-chart line bundle $L \otimes \mathcal{O}(E) \otimes \mathcal{O}(-D_\gamma)$ over a geometric point cuts out a relative effective divisor of degree $g$ inside the smooth locus $U$: on a smooth proper geometrically irreducible fibre of genus $g$ with $L$ algebraically equivalent to zero the Euler characteristic of the twist is again $1$, so the degree of the zero scheme is $g$. It is used by the corresponding statement for families admitting two glued smooth curve degenerations, in the construction of divisorial charts for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_smooth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_I_eq_zeroSchemeIdeal_polarisedChartModule_fibre_of_support_subset_of_twoGluedSmoothCurveDegenerations_of_smooth
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [Flat c] (𝒱 : C.TwoAffineOpenCover) (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g e ρ : ℕ) (hr : g + e = ρ)
    (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγU : Dγ.SupportedIn U)

    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (E.lineBundle ⊗ Dγ.idealModule))).H1 = 1)

    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (SheafOfModules.unit (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).ringCatSheaf)).H1 = g)

    (hgoodU : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → Set.range (pullback.fst c x).base ⊆ (U : Set C))
    (hgoodirr : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      Smooth (pullback.snd c x) → GeometricallyIrreducible (pullback.snd c x))
    (hgred : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)), IsReduced (pullback c x)) :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (_ : Smooth (pullback.snd c (x ≫ t)))
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ ((E.pullbackAlong t (Category.comp_id t)).lineBundle ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ((Scheme.Modules.zeroSchemeIdeal σ).support : Set ↥(pullback c (x ≫ t))) ⊆ ((pullback.fst c (x ≫ t)) ⁻¹ᵁ U : Set ↥(pullback c (x ≫ t))) →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U := by sorry
