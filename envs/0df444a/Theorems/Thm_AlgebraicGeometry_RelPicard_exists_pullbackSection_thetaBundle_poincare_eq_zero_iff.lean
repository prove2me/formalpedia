-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_poincare_eq_zero_iff
-- name    : AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_poincare_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/ba1f9bb7-1f72-5a26-bdd4-cb52b60c745c
-- title:
--   A theta section cutting out the theta locus on J
-- statement:
--   Let $k$ be an algebraically closed field and $c \colon C \to \operatorname{Spec} k$ a proper morphism, smooth of relative dimension $1$, with geometrically integral fibres, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} k \to C$ whose composite with $c$ is the identity. Assume `h𝔉`: for every $m_0$ there is finite map data `FiniteMapData c ε` of degree $m \ge m_0$, i.e. two affine opens $U, V$ covering $C$, with $U$ the complement of the image of $\varepsilon$, functions $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ cutting out $U \cap V$ as a basic open and mutually inverse there, each making the corresponding ring finite over a polynomial algebra, and with all level sets free of rank $m$ over any local base algebra. Let $J$ be a designation of the relative $\mathrm{Pic}^0$, i.e. a scheme `J.P` with a structure morphism `J.toBase` to $\operatorname{Spec} k$ and a zero section, and let $h$ exhibit $J$ as representing the subfunctor of rigidified line bundles on $C \times J'$ cut out by `algEquivZeroCut c ε` (fibrewise algebraic equivalence to zero of the pulled-back bundle on every geometric fibre): $h$ supplies a rigidified Poincaré bundle `h.poincare` satisfying that condition, the universal property, and triviality along the zero section. Assume `J.toBase` smooth, proper and geometrically connected, and let $g$ be a natural number such that every Riemann–Roch genus of $C$ equals $g$: for every extension field $L$ of $k$, every curve model $M$ of $L$ over $k$ with an isomorphism $M.C \cong C$ compatible with the structure morphisms, every divisor $K_c$ and every $g'$, if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ (with $\ell$ the $k$-dimension of the Riemann–Roch space), then $g' = g$. Assume finally $1 \le g$ and $2g \le r$. Then there is a global section $\theta$ of the theta bundle `thetaBundle c ε J.toBase h.poincare r (r + 1 - g)`, the dual of the $(r+1-g)$-th determinant of the pushforward along the second projection of `h.poincare.L` twisted by the $r$-th inverse power of the section ideal, such that for every $k$-point $x$ of $J$ (a morphism in the category over $\operatorname{Spec} k$ from the identity to `J.toBase`) the pullback of $\theta$ along `x.left` vanishes if and only if, for every two-affine open cover $\mathcal{W}$ of the fibre $C_x$, the zeroth Čech cohomology (the kernel of the Čech differential) of the sections of the restriction to $C_x$ of `h.poincare.L` twisted by the $(g-1)$-st inverse power of the section ideal is nontrivial.
--
--   This is the set-theoretic form of Riemann's description of the theta divisor on the Jacobian: the theta bundle attached to the Poincaré bundle carries a section whose zero set among $k$-points is the locus where the twisted fibre $\mathcal{P}_x((g-1)\varepsilon)$ has a nonzero section. It feeds the construction of a nonzero theta section with trivial stabiliser.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_poincare_eq_zero_iff.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian AlgebraicCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_poincare_eq_zero_iff
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
    (hg₁ : 1 ≤ g) (r : ℕ) (hr : 2 * g ≤ r) :
    ∃ θ : 𝟙_ J.P.Modules ⟶ thetaBundle c ε J.toBase h.poincare r (r + 1 - g),
      ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk J.toBase,
        Scheme.Modules.pullbackSection x.left θ = 0 ↔
          ∀ 𝒲 : (pullback (pullback.snd c J.toBase) x.left).TwoAffineOpenCover,
            Nontrivial (𝒲.sectionsOf (fibreAt c J.toBase x.left)
              (fibreModule c J.toBase x.left (h.poincare.L ⊗ sectionTwist c ε J.toBase (g - 1)))).H0 := by sorry
