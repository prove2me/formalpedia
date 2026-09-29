-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
-- name    : AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/76e4333d-ae3a-599c-a308-601fd3542cec
-- title:
--   Block transversals killing H¹ of L(rp-sum vⱼ)
-- statement:
--   Let $K$ be an algebraically closed field, $X$ a scheme with a morphism $x\colon X\to\operatorname{Spec}K$ such that $X$ is integral and $x$ is proper and smooth of relative dimension $1$, and let $g\in\mathbb N$ be characterised by the hypothesis that for every field extension $L/K$, every `CurveModel K L` whose curve is isomorphic to $X$ over $\operatorname{Spec}K$, every divisor $K_c$ and every $g'$, the identity $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$ forces $g'=g$ (here $\ell$ is the $K$-dimension of the Riemann–Roch space and divisors are finitely supported $\mathbb Z$-valued functions on the places of $L/K$). Assume given such data realising $g$: a field extension $F/K$, a curve model $M$ over $K$ with function field $F$, an isomorphism $e\colon M.C\cong X$ with $e$ followed by $x$ equal to $M.\mathrm{toBase}$, and a divisor $K_c$ satisfying the Riemann–Roch identity with this $g$. Assume further: a section $p$ of $x$; a module $L$ on $X$ that is invertible (every point has an open neighbourhood on which $L$ restricts to the unit module) and satisfies `IsAlgEquivZero x L`, i.e. there are a locally of finite type, geometrically integral $T'\to\operatorname{Spec}K$, an invertible module on $X\times_K T'$ and two sections $t_0,t_1$ of $T'$ pulling it back to the unit module and to $L$ respectively; an $r\in\mathbb N$ with $2g\le r+1$; a finite index type $\iota$ and a family $B_i$ of finite sets of sections of $x$, pairwise disjoint, each of cardinality at most $b\ge 1$, with $r\,b^{\,r-g}+(r-g)<\#\iota$; and the numerical hypothesis that for every $v\colon \mathrm{Fin}(r-g)\to\{\text{sections of }x\}$ and every cover $\mathcal V$ of $X$ by two affine opens with affine intersection, the two-term Čech complex of $K$-sections of $(\ker p)^{r\,\vee}\otimes(\prod_j \ker v_j)$ has $\dim_K H^0-\dim_K H^1=1$, where $\ker q$ denotes the module of the ideal sheaf of a section and $(\cdot)^\vee$ its dual. Then there exists an injective $a\colon\mathrm{Fin}(r-g)\to\iota$ such that for every choice $v_j\in B_{a(j)}$ and every such two-chart cover $\mathcal V$, the first Čech cohomology of $L\otimes\bigl((\ker p)^{r\,\vee}\otimes\prod_j\ker v_j\bigr)$ is a subsingleton.
--
--   In classical terms this says that an invertible sheaf algebraically equivalent to zero lies in the Picard chart $U_\gamma=\{L: H^1(L(rp-\gamma))=0\}$ simultaneously for every transversal $\gamma=(v_1,\dots,v_{r-g})$ of a suitably large family of pairwise disjoint blocks of $K$-points, the pigeonhole input being $r\,b^{r-g}+(r-g)<\#\iota$. It is the one-geometric-fibre case used by [`AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre`](thm.html#AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_of_blocks_of_smooth_fibre) in the construction of charts for the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_injective_forall_subsingleton_H1_sectionsOf_tensor_of_isAlgEquivZero_of_lt_card
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x = M.toBase)
    (Kc : Divisor K F) (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (r : ℕ) (hr : 2 * g ≤ r + 1)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (B : ι → Finset {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _})
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : r * b ^ (r - g) + (r - g) < Fintype.card ι)
    (hχ : ∀ (v : Fin (r - g) → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}) (𝒱 : X.TwoAffineOpenCover),
      (Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf x (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module)).H1 = 1) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ v : Fin (r - g) → {q : Spec (CommRingCat.of K) ⟶ X // q ≫ x = 𝟙 _}, (∀ j, v j ∈ B (a j)) →
        ∀ 𝒱 : X.TwoAffineOpenCover,
          Subsingleton (𝒱.sectionsOf x (L ⊗ (((p.ker) ^ r).invModule ⊗ (∏ j, (v j).1.ker).module))).H1 := by sorry
