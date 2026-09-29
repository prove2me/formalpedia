-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/d0c75cad-4622-5d60-8a58-3c9fc19d78fb
-- title:
--   Additivity of the Čech Euler characteristic in L ⊗ L'
-- statement:
--   Let $K$ be an algebraically closed field and let $x : X \to \operatorname{Spec} K$ be a morphism from an integral scheme $X$ which is proper and smooth of relative dimension $1$ over $K$. Let $L$ and $L'$ be sheaves of modules on $X$ satisfying `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ such that the pullback of the sheaf along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf $\mathcal{O}_U$. Let $\mathcal V$ be a `TwoAffineOpenCover` of $X$: two opens $U_0, U_1$, both affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. For a sheaf of modules $M$ the datum $\mathcal V.\mathrm{sectionsOf}\,x\,M$ consists of the $K$-modules $\Gamma(M, U_0)$, $\Gamma(M, U_1)$, $\Gamma(M, U_0 \sqcap U_1)$ (the $K$-structure coming from $x$) together with the two restriction maps; its `H0` is the kernel and its `H1` the cokernel of the two-chart Čech differential $(m_0, m_1) \mapsto r_1(m_1) - r_0(m_0)$. Writing $\chi(M) = \dim_K H^0 - \dim_K H^1 \in \mathbb Z$ for these, the conclusion is $\chi(L \otimes L') = \chi(L) + \chi(L') - \chi(\mathcal{O}_X)$, where $\mathcal{O}_X$ is the unit sheaf `SheafOfModules.unit X.ringCatSheaf` and $L \otimes L'$ is the monoidal product in `X.Modules`.
--
--   This is the additivity of the degree of invertible sheaves on a smooth proper curve, in the form $\chi(L \otimes L') = \chi(L) + \chi(L') - \chi(\mathcal{O}_X)$, with cohomology computed by a two-chart Čech complex for an affine cover by two opens. It is used in the study of the relative Picard functor, for instance in the arguments bounding $\dim_K H^1$ of tensor powers and in the identification of relative effective Cartier divisors on degenerating families of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_eulerChar_sectionsOf_tensor_eq_add_sub.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eulerChar_sectionsOf_tensor_eq_add_sub
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (L L' : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (𝒱 : X.TwoAffineOpenCover) :
    ((Module.finrank K (𝒱.sectionsOf x (L ⊗ L')).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x (L ⊗ L')).H1)
      = ((Module.finrank K (𝒱.sectionsOf x L).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x L).H1)
        + ((Module.finrank K (𝒱.sectionsOf x L').H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x L').H1)
        - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
            - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1) := by sorry
