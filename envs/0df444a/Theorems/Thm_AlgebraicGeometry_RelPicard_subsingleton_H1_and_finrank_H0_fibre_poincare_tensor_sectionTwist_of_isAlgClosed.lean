-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist_of_isAlgClosed
-- name    : AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/fc671570-214c-59ad-a04d-f83dcb9d014e
-- title:
--   Geometric fibres of the twisted Poincaré bundle: H¹=0, h⁰=r+1-g
-- statement:
--   Let $R$ be a commutative ring and $c \colon C \to \operatorname{Spec} R$ a proper morphism, smooth of relative dimension one and geometrically integral, equipped with a section $\varepsilon$ (a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity). Let $D$ consist of a scheme $D.P$ with a structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the rigidified line bundles on $C$ that are fibrewise algebraically equivalent to zero: $h$ provides a rigidified invertible module $h.\mathrm{poincare}$ on $C \times_{R} D.P$ lying in the condition `algEquivZeroCut c ε`, the universal property for such bundles, and triviality of its pullback along the zero section. Let $g$ be a natural number such that for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field extension $L$ of $k$, every `CurveModel k L` whose underlying scheme is isomorphic to the fibre $C \times_{R} \operatorname{Spec} k$ compatibly with the structure morphisms, and every divisor $K_c$ and natural $g'$ satisfying $\ell(D') - \ell(K_c - D') = \deg D' + 1 - g'$ for all divisors $D'$, one has $g' = g$. Let $r$ be a natural number with $2g \le r + 1$. Then for every algebraically closed field $k$, every point $s \colon \operatorname{Spec} k \to D.P$ and every cover $\mathcal{W}$ of the fibre $(C \times_{R} D.P) \times_{D.P} \operatorname{Spec} k$ by two affine opens with affine intersection, the two-term Čech complex of sections of the pullback to that fibre of $h.\mathrm{poincare}.L \otimes ((\ker \varepsilon_{D.P})^{r})^{\vee}$ has subsingleton $H^1$, and its $H^0$ has $k$-dimension $r + 1 - g$ (truncated subtraction of naturals).
--
--   This is the Riemann–Roch computation for the twisted Poincaré bundle $\mathcal{P}(r\varepsilon)$ on the geometric fibres of the relative Picard scheme: for $r \ge 2g-1$ the fibre is a degree-$r$ line bundle on a smooth proper curve of genus $g$, so its $H^1$ vanishes and its $H^0$ has dimension $r+1-g$. It is the geometric-point case feeding the statement for arbitrary field-valued points, which yields local freeness of the Picard bundle used in the construction of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra MonoidalCategory
  GoodReductionJacobian AlgebraicCurve

theorem AlgebraicGeometry.RelPicard.subsingleton_H1_and_finrank_H0_fibre_poincare_tensor_sectionTwist_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (r : ℕ) (hr : 2 * g ≤ r + 1) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ D.P)
      (𝒲 : (pullback (pullback.snd c D.toBase) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c D.toBase s)
          (fibreModule c D.toBase s (h.poincare.L ⊗ sectionTwist c ε D.toBase r))).H0 = r + 1 - g := by sorry
