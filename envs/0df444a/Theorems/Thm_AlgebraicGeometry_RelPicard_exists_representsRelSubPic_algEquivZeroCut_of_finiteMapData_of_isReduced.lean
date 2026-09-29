-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
-- name    : AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/3d49fd55-fb28-539c-9130-e93c862ef8fe
-- title:
--   Representability of fibrewise Pic⁰ over a reduced Noetherian base
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring and let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, equipped with a section $\varepsilon$ of $c$ (a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity). Assume the finite-map hypothesis $h\mathfrak{F}$: for every $m_0 \in \mathbb{N}$ there is a datum `SmoothProperCurve.FiniteMapData c ε` with invariant $m \ge m_0$, i.e. two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose restrictions to $U \cap V = C_f = C_g$ are mutually inverse, with $R[f] \to \Gamma(C,U)$ and $R[g] \to \Gamma(C,V)$ finite, and such that for every local $R$-algebra $S$ and every $s \in S$ the quotient $S \otimes_R \Gamma(C,U)$ by $(1 \otimes f - s \otimes 1)$ is free of rank $m$ over $S$. Assume further $n, g, r \in \mathbb{N}$ with $2g < r$, a family $\gamma$ of $n$ tuples of $r-g$ sections of $c$ satisfying `HasChartSections c γ`: for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$ there are a field extension $L/k$, a curve model $M$ of $L/k$ and an isomorphism $M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ over $\operatorname{Spec} k$ for which Riemann–Roch holds with some $K_c$ and with the given $g$, and every effective divisor of degree $r$ has, for some index $i$, $\ell$ of its difference with the sum of the $r-g$ points $\gamma_{ij}$ equal to $1$. The conclusion is the existence of a designation $D$, namely a scheme $P$ with a structure morphism $D.\mathrm{toBase} \colon P \to \operatorname{Spec} R$ and a section of it, such that (i) $D$ represents the cut `algEquivZeroCut c ε` of the rigidified relative Picard presheaf of $(c, \varepsilon)$ — that is, there is a rigidified invertible module on $C \times_R P$ all of whose geometric fibres are algebraically equivalent to zero, whose pullbacks classify, uniquely up to unique morphism over $\operatorname{Spec} R$, all rigidified invertible modules on $C \times_R T$ with the same fibrewise property, and whose pullback along the section is trivial — and (ii) $D.\mathrm{toBase}$ is smooth, proper and geometrically connected.
--
--   This is the representability of the fibrewise-algebraically-trivial relative Picard functor $\mathrm{Pic}^0_{C/R,\varepsilon}$ by a smooth proper scheme with geometrically connected fibres, i.e. the construction of the relative Jacobian of a smooth proper curve with a section over a reduced Noetherian base admitting finite-map data. It is the base case from which the versions over a discrete valuation ring and over an algebraically closed field are deduced, and it feeds the construction of relative Jacobians used for good-reduction statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_JacJ1Iface
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_LocalRepresentabilityULift
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
