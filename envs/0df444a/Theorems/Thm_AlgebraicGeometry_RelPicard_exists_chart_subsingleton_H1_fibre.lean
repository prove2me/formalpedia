-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre
-- name    : AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/37d0ad2a-5913-5c44-a4d8-8119e1264e8f
-- title:
--   Milne charts cover Pic⁰: some chart kills H¹
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c : C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, equipped with a section $\varepsilon$, that is, a morphism $\operatorname{Spec} R \to C$ splitting $c$. Fix naturals $n, g, r$ with $2g < r$ and assume: (i) for every algebraically closed field $k$, every $k$-point $s$ of $\operatorname{Spec} R$, every extension field $L/k$, every `CurveModel` $M$ for $L/k$ together with an isomorphism $e : M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ over $\operatorname{Spec} k$, and every divisor $K_c$ and natural $g'$, if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ holds for all divisors $D$ of $M$, then $g' = g$; (ii) a family $\gamma : \mathrm{Fin}\,n \to \mathrm{Fin}\,(r-g) \to$ (sections of $c$) satisfying `HasChartSections c γ`, i.e. over every algebraically closed $k$-point of $\operatorname{Spec} R$ the geometric fibre admits a curve model in which Riemann–Roch holds with genus $g$ and, for every effective divisor of degree $r$, some index $i$ makes $\ell\bigl(D - \sum_j [\gamma_{ij}]\bigr) = 1$; (iii) relative effective Cartier divisors $D_{\gamma_i}$ of degree $r-g$ on $C \times_R \operatorname{Spec} R$ over the identity of $\operatorname{Spec} R$ whose ideals are the products $\prod_j \ker(\Gamma_{\gamma_{ij}})$ of the graph ideals of the $\gamma_{ij}$; (iv) for each $i$, each algebraically closed field $k$, each $k$-point $x$ of $\operatorname{Spec} R$ and each cover of the fibre by two affine opens, the Čech Euler characteristic $h^0 - h^1$ of the fibre of $\mathcal{O}(r\varepsilon) \otimes \mathcal{I}_{D_{\gamma_i}}$ equals $1$, where $\mathcal{O}(r\varepsilon)$ denotes the dual of the $r$-th power of the ideal of the rigidifying section and $\mathcal{I}_{D_{\gamma_i}}$ the ideal module of $D_{\gamma_i}$. Then for every $t : T \to \operatorname{Spec} R$, every rigidified line bundle $L$ on $C \times_R T$ (an invertible module with a trivialisation along the section $\varepsilon_T$) satisfying `FibrewiseAlgEquivZero`, every field $k$ and every $k$-point $s$ of $T$, there is an index $i$ such that for every cover of the fibre $(C\times_R T)\times_T \operatorname{Spec} k$ by two affine opens the first Čech cohomology of the fibre of $L \otimes \mathcal{O}(r\varepsilon_T) \otimes \mathcal{I}_{D_{\gamma_i,T}}$, the cokernel of the difference of the two restriction maps, is a subsingleton.
--
--   This is the joint surjectivity of Milne's open charts onto the degree-zero part of the relative Picard functor: every point of $T$ with values in a field lies in the locus where one of the finitely many chart twists has vanishing $H^1$ on the corresponding fibre. It is used in the construction of the open charts covering the algebraic-equivalence-zero part of the relative Picard presheaf, which invokes it through [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_chart_subsingleton_H1_fibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_chart_subsingleton_H1_fibre
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (hγ : HasChartSections c γ)
    (Dγ : Fin n → RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of R))))
    (hDγ : ∀ i, (Dγ i).I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2))
    (hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) :
    ∃ i : Fin n, ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
        (L.L ⊗ (sectionTwist c ε t r ⊗ ((Dγ i).pullbackAlong t (Category.comp_id t)).idealModule)))).H1 := by sorry
