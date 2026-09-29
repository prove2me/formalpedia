-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nontrivial_H0_sectionsOf_of_le_eulerChar_sub
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d9a83522-9d67-5cb2-978f-e1f79963c2ec
-- title:
--   Riemann's inequality in two-chart Čech form
-- statement:
--   Let $K$ be an algebraically closed field, $X$ a scheme with a morphism $x \colon X \to \operatorname{Spec} K$ such that $X$ is integral, $x$ is proper and $x$ is smooth of relative dimension $1$. Let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of $U$, and let $\mathcal{V}$ be a two-chart affine open cover of $X$, i.e. opens $U_0, U_1$ with $U_0$, $U_1$ and $U_0 \cap U_1$ affine and $U_0 \cup U_1 = X$. For a sheaf of modules $\mathcal{F}$, write $\check H^0$ for the kernel and $\check H^1$ for the cokernel of the $K$-linear map $\Gamma(\mathcal{F}, U_0) \times \Gamma(\mathcal{F}, U_1) \to \Gamma(\mathcal{F}, U_0 \cap U_1)$, $(m_0, m_1) \mapsto m_1|_{U_0 \cap U_1} - m_0|_{U_0 \cap U_1}$, the $K$-structures coming from $x$. Assume, as an inequality of integers,
--   $$\dim_K \check H^1(\mathcal{O}_X) \le \bigl(\dim_K \check H^0(M) - \dim_K \check H^1(M)\bigr) - \bigl(\dim_K \check H^0(\mathcal{O}_X) - \dim_K \check H^1(\mathcal{O}_X)\bigr),$$
--   where $\mathcal{O}_X$ denotes the unit sheaf of modules on $X$. Then $\check H^0(M)$ is nontrivial, i.e. it contains a nonzero element.
--
--   This is Riemann's inequality $h^0(M) \ge \deg M + 1 - g$ for a line bundle on a smooth proper curve, written entirely in the two-chart Čech currency with $\deg M$ replaced by the Euler-characteristic difference $\chi(M) - \chi(\mathcal{O}_X)$ and $g$ by $\dim_K \check H^1(\mathcal{O}_X)$. It serves the analysis of the relative Picard functor, being used in the criteria for a rigidified line bundle to be trivial and in the Euler-characteristic characterisation of triviality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nontrivial_H0_sectionsOf_of_le_eulerChar_sub.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ)
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Nontrivial (𝒱.sectionsOf x M).H0 := by sorry
