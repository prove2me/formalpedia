-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
-- name    : AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/73641204-c114-5cf0-bab4-e02062721654
-- title:
--   Twisting by an invertible ideal sheaf raises χ by r
-- statement:
--   Let $k$ be a field and let $x \colon X \to \operatorname{Spec} k$ be a proper morphism of schemes. Let $I$ be a quasi-coherent ideal sheaf datum on $X$ which is invertible in the sense of `IsInvertible`: for every point of $X$ there are an affine open $U$ and $f \in \Gamma(X,U)$ with the point in $X.\mathrm{basicOpen}\, f$, together with a non-zero-divisor $g$ of $\Gamma(X, X.\mathrm{affineBasicOpen}\, f)$ such that the ideal of $I$ on $X.\mathrm{affineBasicOpen}\, f$ is $(g)$. Let $r$ be a natural number, assume the composite of the closed immersion $I.\mathrm{subscheme\iota}$ of the subscheme cut out by $I$ with $x$ satisfies `IsFinite`, and assume its rank `finrank t` equals $r$ at every point $t$ of $\operatorname{Spec} k$. Let $L$ be a sheaf of $\mathcal O_X$-modules that is invertible, i.e. each point of $X$ has an open neighbourhood $W$ with the restriction of $L$ to $W$ isomorphic to the unit sheaf, and let $\mathcal V$ be a cover of $X$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. For a module $M$, write $\check H^0$ and $\check H^1$ for the kernel and the cokernel of the $k$-linear map $\Gamma(M,U_0) \times \Gamma(M,U_1) \to \Gamma(M, U_0 \sqcap U_1)$, $(m_0,m_1) \mapsto m_1|_{U_0 \cap U_1} - m_0|_{U_0 \cap U_1}$. Then, as an identity in $\mathbb Z$ between `Module.finrank` values over $k$, $$\dim \check H^0(\mathcal V, L \otimes I.\mathrm{invModule}) - \dim \check H^1(\mathcal V, L \otimes I.\mathrm{invModule}) = \dim \check H^0(\mathcal V, L) - \dim \check H^1(\mathcal V, L) + r,$$ where $I.\mathrm{invModule}$ is the dual of the module $I.\mathrm{module}$, the kernel of the map from the unit sheaf to the pushforward of the unit along $I.\mathrm{subscheme\iota}$.
--
--   This is the additivity of the Euler characteristic under twisting by an effective Cartier divisor, $\chi(\mathcal L(Z)) = \chi(\mathcal L) + \deg Z$, the easy half of Riemann–Roch, formulated for the two-chart Čech complex attached to a cover of $X$ by two affine opens with affine intersection. It is used to compute Euler characteristics and degrees of line bundles twisted by relative effective Cartier divisors, and thence in the study of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_sectionsOf_tensor_invModule_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x]
    {I : X.IdealSheafData} (hI : I.IsInvertible) {r : ℕ}
    (hZ : IsFinite (I.subschemeι ≫ x))
    (hdeg : ∀ t : Spec (CommRingCat.of k), (I.subschemeι ≫ x).finrank t = r)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (𝒱 : X.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf x (L ⊗ I.invModule)).H1
      = (Module.finrank k (𝒱.sectionsOf x L).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x L).H1 + r := by sorry
