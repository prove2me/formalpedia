-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso
-- name    : AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/8fd4e7c0-b0cb-54b8-9782-a55cb5f72a19
-- title:
--   Theta bundle of a translate by sum Pᵢ-dε
-- statement:
--   Let $k$ be a field and $c\colon C\to\operatorname{Spec}k$ a proper morphism, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a morphism $\operatorname{Spec}k\to C$ splitting $c$. Assume `h𝔉`: for every $m_0$ there is a datum `SmoothProperCurve.FiniteMapData` for $c,\varepsilon$ (a cover of $C$ by two affine opens $U$, the complement of the image of $\varepsilon$, and $V$, with sections $f\in\Gamma(C,U)$, $g\in\Gamma(C,V)$ cutting out $U\sqcap V$, inverse to one another there, making $\Gamma(C,U)$ and $\Gamma(C,V)$ finite over $k[x]$ and with all level sets of $f$ free of rank $m$) whose invariant $m$ is at least $m_0$. Let $g\in\mathbb N$ satisfy `hg`: whenever $k'$ is algebraically closed, $s\colon\operatorname{Spec}k'\to\operatorname{Spec}k$, $L/k'$ a field extension, $M$ a `CurveModel` of $L$ over $k'$ with an isomorphism $M.C\cong C\times_k\operatorname{Spec}k'$ compatible with the structure morphisms, $K_c$ a divisor and $g'\in\mathbb N$ are such that $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, then $g'=g$. Let $t\colon T\to\operatorname{Spec}k$ be locally of finite type, let $\mathcal M$ be a rigidified line bundle for $(c,\varepsilon)$ over $t$ (an invertible module on $C\times_kT$ trivialised along `rigSection`) satisfying `FibrewiseAlgEquivZero`, let $P_1,\dots,P_d$ be a list $Ps$ of splittings of $c$ over $\operatorname{Spec}k$, and let $\mathcal N$ be a rigidified line bundle over the identity of $\operatorname{Spec}k$ satisfying `FibrewiseAlgEquivZero` and equipped with an isomorphism $\mathcal N.L\cong\bigotimes_i\bigl(\mathcal O(P_i)\otimes\mathcal I(\varepsilon)\bigr)$, the module `pointsSubBasepointModule`. Let $r\in\mathbb N$ with $2g\le r+1$. Then there exists an isomorphism of $T$-modules
--   $$\Theta\bigl(\mathcal M\otimes t^*\mathcal N\bigr)\otimes\bigotimes_{i=1}^{d}(P_i)_T^*\mathcal M\;\cong\;\Theta(\mathcal M),$$
--   where $\Theta(\mathcal F)=\bigl(\det\nolimits_{r+1-g}(\mathrm{pr}_T)_*(\mathcal F.L\otimes(\mathcal I(\varepsilon)^r)^{-1})\bigr)^{\vee}$ is `thetaBundle c ε t 𝓕 r (r+1-g)`, $t^*\mathcal N$ is the pullback of $\mathcal N$ along $t$, and the tensor product over the list is formed by `List.foldr` from the pullbacks of $\mathcal M.L$ along the sections `rigSection c t Pᵢ`, starting from the unit module of $T$.
--
--   This is the multiplicativity, in the list of points, of the correction factor comparing the theta bundle of a family in the algebraically-equivalent-to-zero cut with that of its translate by the class of $\sum_iP_i-d\varepsilon$; it is the mechanism behind the theorem of the square for Picard bundles on a Jacobian. It feeds the comparison of theta bundles under translation by an arbitrary fibrewise algebraically trivial rigidified line bundle, `nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso.lean

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

theorem AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointsSubBasepoint_tensor_foldr_pullback_iso
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
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k)))) (hN : FibrewiseAlgEquivZero N)
    (eN : N.L ≅ pointsSubBasepointModule (a := c) ε Ps)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        Ps.foldr (fun P A => (Scheme.Modules.pullback (rigSection c t P)).obj M.L ⊗ A) (𝟙_ T.Modules) ≅
      thetaBundle c ε t M r (r + 1 - g)) := by sorry
