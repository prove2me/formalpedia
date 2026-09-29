-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
-- name    : AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/7bec6867-5eee-58a2-ac92-f238fb9159ba
-- title:
--   Theorem of the square for relative theta bundles
-- statement:
--   Let $k$ be an algebraically closed field and let $c\colon C\to\operatorname{Spec}k$ be proper, smooth of relative dimension one and geometrically integral, equipped with a section $\varepsilon$ of $c$ over $\operatorname{Spec}k$ (a morphism $\operatorname{Spec}k\to C$ composing with $c$ to the identity). Assume the data `SmoothProperCurve.FiniteMapData c ε` of two affine charts with finite coordinate maps exists with arbitrarily large invariant $m$, and let $g\in\mathbb N$ be such that every $g'$ occurring in a Riemann–Roch identity $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ (for all divisors $D$) for a `CurveModel k' L` whose curve is isomorphic, compatibly with the structure maps, to the base change of $c$ along any $\operatorname{Spec}k'\to\operatorname{Spec}k$ with $k'$ algebraically closed, equals $g$. Let $t\colon T\to\operatorname{Spec}k$ be locally of finite type. Let $M$ be a rigidified line bundle on $C\times_k T$, i.e. an invertible module on `pullback c t` trivialised along the rigidifying section, and let $N_1,N_2$ be rigidified line bundles for the base $\mathrm{id}_{\operatorname{Spec}k}$; assume all three satisfy `FibrewiseAlgEquivZero`, that is, for every algebraically closed $k'$ and every point $\operatorname{Spec}k'\to$ base, the restriction of the underlying module to the corresponding geometric fibre of the curve satisfies `IsAlgEquivZero`. Let $r\in\mathbb N$ with $2g\le r+1$, and write $\Theta(\mathcal F)$ for `thetaBundle c ε t 𝓕 r (r+1-g)`, the dual of the $(r+1-g)$-th determinant of the Picard bundle of $\mathcal F$ twisted by `sectionTwist c ε t r`. Then there exists an isomorphism of modules on $T$
--   $$\Theta(M\otimes N_1^T)\otimes\Theta(M\otimes N_2^T)\;\cong\;\Theta\bigl(M\otimes(N_1\otimes N_2)^T\bigr)\otimes\Theta(M),$$
--   where $(-)^T$ denotes `pullbackAlong ⟨t, Category.comp_id t⟩`, the pullback of a rigidified bundle on the curve to $C\times_k T$, and the tensor products of rigidified bundles are formed via `RigidifiedLineBundle.tensor`.
--
--   This is the Picard-bundle form of the theorem of the square for the theta bundle attached to a smooth proper curve with a marked point: bilinearity of $\mathcal F\mapsto\Theta(\mathcal F)$ in twists by degree-zero line bundles pulled back from the curve. It is used by [`AlgebraicGeometry.RelPicard.nonempty_translate_thetaBundle_tensor_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_translate_thetaBundle_tensor_iso) to obtain the translation relation $T_x^{*}\Theta\otimes T_y^{*}\Theta\cong T_{xy}^{*}\Theta\otimes\Theta$ on the relative Picard scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pullbackAlong_tensor_iso_of_fibrewiseAlgEquivZero
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
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
    (N₁ N₂ : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (hN₁ : FibrewiseAlgEquivZero N₁) (hN₂ : FibrewiseAlgEquivZero N₂)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    Nonempty (
      thetaBundle c ε t (M.tensor (N₁.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t (M.tensor (N₂.pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ≅
      thetaBundle c ε t (M.tensor ((N₁.tensor N₂).pullbackAlong ⟨t, Category.comp_id t⟩)) r (r + 1 - g) ⊗
        thetaBundle c ε t M r (r + 1 - g)) := by sorry
