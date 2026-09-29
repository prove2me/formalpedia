-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
-- name    : AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/0bde3e7f-d9a7-5bbb-a227-e82bce96bc49
-- title:
--   Fibrewise H¹=0 and h⁰=r+1-g over any field
-- statement:
--   Let $R$ be a commutative ring and let $c\colon C\to\operatorname{Spec}R$ be proper, smooth of relative dimension one and geometrically integral, equipped with a section $\varepsilon$ (a morphism $\operatorname{Spec}R\to C$ whose composite with $c$ is the identity). Let $g$ be a natural number subject to the following constancy hypothesis: whenever $k$ is an algebraically closed field, $s\colon\operatorname{Spec}k\to\operatorname{Spec}R$ a morphism, $L/k$ a field extension, $M$ a `CurveModel` for $k$ and $L$ (an integral scheme, proper and smooth of relative dimension one over $\operatorname{Spec}k$, with function field identified with $L$ compatibly with $k$, and with closed points in bijection with the places of $L/k$ in the manner recorded in the structure), $e\colon M.C\cong C\times_{\operatorname{Spec}R}\operatorname{Spec}k$ an isomorphism over $\operatorname{Spec}k$ (that is, $e$ followed by the second projection is $M.\mathrm{toBase}$), $K_c$ a divisor of $L/k$ and $g'$ a natural number with $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, then $g'=g$. Let $t\colon T\to\operatorname{Spec}R$ be a scheme over $R$ and let $M$ be a rigidified line bundle for $c$, $\varepsilon$ and $t$: an invertible module $M.L$ on $C\times_{\operatorname{Spec}R}T$ together with a trivialisation of its pullback along the rigidifying section $T\to C\times_{\operatorname{Spec}R}T$ determined by $\varepsilon$. Assume `FibrewiseAlgEquivZero M`, i.e. for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$ the pullback of $M.L$ to the fibre satisfies `IsAlgEquivZero`: there is a geometrically integral base $T'$ locally of finite type over $k$, an invertible module on the corresponding pullback, and two sections of $T'$ over $k$ along which that module becomes trivial, respectively isomorphic to the fibre of $M.L$. Let $r$ be a natural number with $2g\le r+1$. Then for every field $k$, every $s\colon\operatorname{Spec}k\to T$ and every covering $\mathcal W$ of the fibre $(C\times_{\operatorname{Spec}R}T)\times_Ts$ by two affine opens with affine intersection and union everything, the two-chart Čech complex of the restriction to that fibre of $M.L\otimes\mathcal O(r\varepsilon_T)$ — where $\mathcal O(r\varepsilon_T)$ is `sectionTwist`, the dual of the module of the $r$-th power of the ideal sheaf cut out by the rigidifying section — has $H^1$ a subsingleton, and its $H^0$ has $k$-dimension $r+1-g$ (truncated subtraction of natural numbers, which is harmless since $g\le r+1$).
--
--   This is the Riemann–Roch input for Picard bundles in the relative setting: a fibrewise degree-zero line bundle twisted by $r$ times the section has, on each fibre over a field-valued point, vanishing first Čech cohomology and $h^0=r+1-g$, computed by any cover of the fibre by two affine opens. It is the version over an arbitrary residue field, and it feeds the construction of theta bundles and the comparison of the relative Picard functor with its representing scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
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
  AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_tensor_sectionTwist_of_fibrewiseAlgEquivZero
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t)
    (hM : FibrewiseAlgEquivZero M)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 =
          r + 1 - g := by sorry
