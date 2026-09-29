-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
-- name    : AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/dc023f08-88af-594a-8dae-29b1f86fed5d
-- title:
--   Algebraic equivalence to zero equals equality of Čech Euler characteristics
-- statement:
--   Let $K$ be an algebraically closed field, $X$ an integral scheme and $x \colon X \to \operatorname{Spec} K$ a morphism that is proper and smooth of relative dimension $1$. Let $M$ be a sheaf of modules on $X$ that is invertible, in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of $\mathcal O_U$, and let $\mathcal V$ consist of two affine opens $U_0, U_1 \subseteq X$ with affine intersection and $U_0 \sqcup U_1 = \top$. For a module $N$ on $X$, $\mathcal V$ produces the two-term Čech datum with $K$-modules $\Gamma(N, U_0)$, $\Gamma(N, U_1)$, $\Gamma(N, U_0 \sqcap U_1)$ and the difference of restrictions $(m_0, m_1) \mapsto m_1|_{U_0 \sqcap U_1} - m_0|_{U_0 \sqcap U_1}$, whose kernel is $H^0$ and whose cokernel is $H^1$. The assertion is an equivalence. The first side says that $M$ is algebraically equivalent to zero: there exist a scheme $T'$, a morphism $h \colon T' \to \operatorname{Spec} K$ that is locally of finite type and geometrically integral, an invertible module $\mathcal M$ on $X \times_{\operatorname{Spec} K} T'$, and two $K$-points $t_0, t_1$ of $T'$ (morphisms $\operatorname{Spec} K \to T'$ over $\operatorname{Spec} K$) such that the pullback of $\mathcal M$ along the base change of $t_0$ is isomorphic to the unit module on $X \times_{\operatorname{Spec} K} \operatorname{Spec} K$, while the pullback along the base change of $t_1$ is isomorphic to the pullback of $M$ along the first projection. The second side is the equality of integers $\dim_K H^0(\mathcal V, M) - \dim_K H^1(\mathcal V, M) = \dim_K H^0(\mathcal V, \mathcal O_X) - \dim_K H^1(\mathcal V, \mathcal O_X)$, with $\mathcal O_X$ the unit module of the structure sheaf.
--
--   This is the characterisation of line bundles of degree zero on a smooth proper integral curve over an algebraically closed field: algebraic equivalence to zero is equivalent to having the same Euler characteristic as the structure sheaf, with Euler characteristics computed from a two-chart Čech complex. It is used in the theory of relative effective Cartier divisors and relative Picard groups for curve models, for instance in identifying line bundles that become trivial after pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.RelPicard NeronModelInfra
open AlgebraicGeometry

theorem AlgebraicGeometry.RelPicard.isAlgEquivZero_iff_eulerChar_sectionsOf_eq
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) :
    IsAlgEquivZero x M ↔
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
        (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ) -
          Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 := by sorry
