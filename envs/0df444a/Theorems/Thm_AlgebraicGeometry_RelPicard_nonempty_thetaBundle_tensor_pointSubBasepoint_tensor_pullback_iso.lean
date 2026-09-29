-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/444987f6-54f1-5e7c-a9c0-1dc206fe10cf
-- title:
--   Theta bundle twisted by 𝒪(P-ε)
-- statement:
--   Let $k$ be a field and $c\colon C\to\operatorname{Spec}k$ a proper morphism, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a $k$-point of $C$, i.e. a morphism $\operatorname{Spec}k\to C$ splitting $c$. Assume `h𝔉`: for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` for $c$ and $\varepsilon$ of degree $m\ge m_0$ (a two-chart description of $C$ by affine opens $U$, the complement of $\varepsilon$, and $V$, with mutually inverse functions $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ on $U\cap V$, finiteness of both charts over polynomial algebras, and all level sets of $f$ free of rank $m$). Let $g\in\mathbb N$ satisfy `hg`: whenever a Riemann–Roch formula $\ell(D)-\ell(K-D)=\deg D+1-g'$ holds for all divisors of a `CurveModel` over an algebraically closed field identified, compatibly with the structure morphisms, with a geometric fibre of $c$, then $g'=g$. Let $t\colon T\to\operatorname{Spec}k$ be locally of finite type, $M$ a rigidified line bundle on $C\times_kT$ (an invertible module trivialised along the section $\varepsilon_T$) satisfying `FibrewiseAlgEquivZero`, $P$ a $k$-point of $C$, and $N$ a rigidified line bundle on $C\times_k\operatorname{Spec}k$ satisfying `FibrewiseAlgEquivZero` whose underlying module is isomorphic to $\mathcal O(P)\otimes\mathcal I_\varepsilon$. Let $r\in\mathbb N$ with $2g\le r+1$. Writing $\Theta(\mathcal F)$ for the dual of the $(r+1-g)$-th determinant of $\pi_*(\mathcal F\otimes(\mathcal I_{\varepsilon_T}^{\,r})^{-1})$, where $\pi$ is the projection to $T$, the conclusion asserts that the set of isomorphisms $$\Theta(M\otimes N_T)\otimes P_T^{*}M\;\cong\;\Theta(M)$$ of modules on $T$ is nonempty, $N_T$ being the pullback of $N$ along $t$ and $P_T$ the constant section of $\pi$ determined by $P$.
--
--   This is the one-point step of the Picard-bundle induction underlying the theorem of the square: translating a rigidified line bundle by $\mathcal O(P-\varepsilon)$ changes the associated theta bundle only by the fibre of the bundle at the constant section $P_T$. It is used by [`AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso), which iterates it over a finite list of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M)
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k)))) (hN : FibrewiseAlgEquivZero N)
    (eN : N.L ≅ pointSubBasepointModule (a := c) P ε)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        (Scheme.Modules.pullback (rigSection c t P)).obj M.L ≅
      thetaBundle c ε t M r (r + 1 - g)) := by sorry
