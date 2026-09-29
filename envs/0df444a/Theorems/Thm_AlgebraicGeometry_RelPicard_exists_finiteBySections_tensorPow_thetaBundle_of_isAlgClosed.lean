-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed
-- name    : AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/335f7f66-8376-5a80-ba9d-e69bb57e9659
-- title:
--   A tensor power of the theta bundle is finite by sections
-- statement:
--   Let $k$ be an algebraically closed field and let $c\colon C\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, equipped with a $k$-point $\varepsilon$, i.e. a morphism $\operatorname{Spec}k\to C$ whose composite with $c$ is the identity. Assume the chart hypothesis $h\mathfrak F$: for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ with $m\ge m_0$, that is, affine opens $U,V$ with $U\sqcup$-sup $V=\top$, $U$ exactly the complement of the image of $\varepsilon$, sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ with $U\sqcap V$ equal to both basic opens and $f\cdot g=1$ there, $f$ and $g$ finite over the polynomial algebra, and all level sets of $f$ over local base algebras finite free of rank $m$. Let $J$ be a `RelativePic0Designation` for $c$ (a scheme $J.P$ with structure morphism $J$`.toBase` to $\operatorname{Spec}k$ and a zero section), and let $h$ witness that $J$ represents the cut of the rigidified relative Picard presheaf of $(C,\varepsilon)$ by fibrewise algebraic equivalence to zero: $h$ provides a Poincaré rigidified line bundle `h.poincare` in that cut, the universal property for rigidified line bundles satisfying the condition, and the triviality of the pullback along the zero section. Assume $J$`.toBase` smooth, proper and geometrically connected. Let $g\in\mathbb N$ be such that any $g'$ satisfying the Riemann–Roch identity $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, for some curve model of $C$ over an extension $L/k$ and some $K_c$, equals $g$; and let $r$ satisfy $2g\le r$. Then there is $n\in\mathbb N$ such that the $n$-th tensor power of $\Theta=$ `thetaBundle c ε J.toBase h.poincare r (r + 1 - g)`, the dual of the $(r+1-g)$-th determinant of the Picard bundle of the Poincaré bundle twisted by $r\varepsilon$, is finite by sections over $J$`.toBase` — there are $N$ and a projective presentation of it over $\operatorname{Spec}k$ of dimension $N$ whose associated morphism to $\operatorname{Proj}$ is finite — and, for every ordered affine cover $\mathcal W$ of $J.P$ (a finite linearly ordered family of affine opens covering $J.P$), the first Čech cohomology `HSucc 𝒲 0` of the $\mathcal O$-module presheaf of sections of that tensor power is a subsingleton.
--
--   This is the projectivity-of-the-Jacobian step: a suitable power of the theta bundle attached to the Picard bundle $(\mathrm{pr}_2)_*(\mathcal P(r\varepsilon))$ maps $J$ finitely to projective space and has vanishing first Čech cohomology on affine covers. It is the algebraically closed base case feeding the construction of a finite projective presentation of the Jacobian of a smooth proper curve over a general base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hsm : Smooth J.toBase) (hpr : IsProper J.toBase) (hgc : GeometricallyConnected J.toBase)
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ C)
      (_ : e.hom ≫ c = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (r : ℕ) (hr : 2 * g ≤ r) :
    ∃ n : ℕ,
      Scheme.Modules.FiniteBySections
          ((thetaBundle c ε J.toBase h.poincare r (r + 1 - g)).tensorPow n) J.toBase ∧
        ∀ 𝒲 : J.P.OrderedAffineCover,
          Subsingleton
            ((OModulePresheaf.ofModules J.toBase
                ((thetaBundle c ε J.toBase h.poincare r (r + 1 - g)).tensorPow n)).HSucc 𝒲 0) := by sorry
