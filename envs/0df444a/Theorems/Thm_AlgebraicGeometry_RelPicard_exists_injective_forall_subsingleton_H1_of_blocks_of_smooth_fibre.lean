-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c2dcc7b9-4447-5069-a44d-09b770f68ec1
-- title:
--   Block general position on a smooth geometric fibre
-- statement:
--   Let $R$ be a commutative ring, $c\colon C\to\operatorname{Spec}R$ a morphism of schemes, and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec}R\to C$ composing with $c$ to the identity). Let $B_0,\dots,B_{M-1}$ be $R$-algebras with morphisms $z_i\colon\operatorname{Spec}B_i\to C$ over $\operatorname{Spec}R$ whose underlying set-theoretic images are pairwise disjoint, and let $\deg\colon\mathrm{Fin}\,M\to\mathbb N$ satisfy $1\le\deg i\le b$. Let $r,g$ satisfy $2g\le r+1$ and $r\,b^{\,r-g}+(r-g)<M$, and let $\Omega$ be an algebraically closed $R$-algebra field for which the set of $R$-algebra maps $B_i\to\Omega$ is in bijection with $\mathrm{Fin}(\deg i)$. Assume $X:=C\times_{\operatorname{Spec}R}\operatorname{Spec}\Omega$ is an integral scheme and that its projection to $\operatorname{Spec}\Omega$ is proper and smooth of relative dimension $1$. Assume further: for one cover $\mathcal V_0$ of $X$ by two affine opens with affine intersection, the two-chart Čech $H^1$ of the unit module (the quotient of the sections over the intersection by the images of the sections over the two charts) has $\Omega$-dimension $g$; and for every $(r-g)$-tuple $v$ of $\Omega$-points of $X$ sectioning the projection and every such two-chart cover, the Čech Euler characteristic $\dim H^0-\dim H^1$ of the dual of the $r$-th power of the ideal sheaf of the base-changed point $\varepsilon_\Omega$, tensored with the ideal-sheaf module of $\prod_j v_j$, equals $1$. Finally let $L_0$ be a module on $X$ that is invertible (locally on opens covering $X$ its pullback is isomorphic to the unit) and algebraically equivalent to zero over $\operatorname{Spec}\Omega$, in the sense that there are a locally-of-finite-type geometrically integral $T'\to\operatorname{Spec}\Omega$, an invertible module on $X\times_{\operatorname{Spec}\Omega}T'$ and two $\Omega$-points of $T'$ at which it pulls back to the unit and to $L_0$ respectively. Then there is an injective map $a\colon\mathrm{Fin}(r-g)\to\mathrm{Fin}\,M$ such that for every $(r-g)$-tuple $v$ of $\Omega$-points of $X$ sectioning the projection with each $v_j$ factoring through $z_{a(j)}$ via some $R$-algebra map $B_{a(j)}\to\Omega$, and for every cover of $X$ by two affine opens with affine intersection, the two-chart Čech $H^1$ of $L_0$ tensored with the above module is a subsingleton, i.e. vanishes.
--
--   This is the per-fibre "block general position" statement: on a smooth proper geometric fibre of a pointed curve, blocks of $\Omega$-points can be chosen so that $L_0(r\varepsilon-v_1-\dots-v_{r-g})$ has vanishing $H^1$ for every choice of points inside the chosen blocks, with the genus read off from the two-chart Čech cohomology of the structure sheaf via Riemann–Roch on the function field. It supplies the hypothesis needed for the orbit-in-one-chart argument used in the finite étale descent of the relative $\operatorname{Pic}^0$, and is invoked both there and in the version of the block statement built from a pool of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicCurve AlgebraicGeometry.SmoothProperCurve TensorProduct
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {M : ℕ} (B : Fin M → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ C)
    (hz : ∀ i, z i ≫ c = Spec.map (CommRingCat.ofHom (algebraMap R (B i))))
    (hzdisj : Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base))
    (deg : Fin M → ℕ) (hdeg : ∀ i, 1 ≤ deg i) {b : ℕ} (hdegb : ∀ i, deg i ≤ b)
    (r g : ℕ) (hr : 2 * g ≤ r + 1) (hcount : r * b ^ (r - g) + (r - g) < M)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (eB : ∀ i, (B i →ₐ[R] Ω) ≃ Fin (deg i))
    [IsIntegral (pullback c (SmoothProperCurve.specMap R Ω))]
    [IsProper (pullback.snd c (SmoothProperCurve.specMap R Ω))]
    [SmoothOfRelativeDimension 1 (pullback.snd c (SmoothProperCurve.specMap R Ω))]

    (𝒱₀ : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover)
    (hg : Module.finrank Ω (𝒱₀.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
      (𝟙_ (pullback c (SmoothProperCurve.specMap R Ω)).Modules)).H1 = g)
    (hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
        q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _})
      (𝒱 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover),
      (Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
          ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
            (∏ j, (v j).1.ker).module)).H0 : ℤ) -
        Module.finrank Ω (𝒱.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
          ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
            (∏ j, (v j).1.ker).module)).H1 = 1)
    (L₀ : (pullback c (SmoothProperCurve.specMap R Ω)).Modules) (hL₀ : Scheme.Modules.IsInvertible L₀)
    (h0 : IsAlgEquivZero (pullback.snd c (SmoothProperCurve.specMap R Ω)) L₀) :
    ∃ a : Fin (r - g) → Fin M, Function.Injective a ∧
      ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of Ω) ⟶ pullback c (SmoothProperCurve.specMap R Ω) //
          q ≫ pullback.snd c (SmoothProperCurve.specMap R Ω) = 𝟙 _},
        (∀ j, ∃ ψ : B (a j) →ₐ[R] Ω,
          (v j).1 ≫ pullback.fst c (SmoothProperCurve.specMap R Ω) =
            Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ z (a j)) →
        ∀ 𝒲 : (pullback c (SmoothProperCurve.specMap R Ω)).TwoAffineOpenCover,
          Subsingleton (𝒲.sectionsOf (pullback.snd c (SmoothProperCurve.specMap R Ω))
            (L₀ ⊗ ((((sectionFibrePoint ε (SmoothProperCurve.specMap R Ω)).1.ker) ^ r).invModule ⊗
              (∏ j, (v j).1.ker).module))).H1 := by sorry
