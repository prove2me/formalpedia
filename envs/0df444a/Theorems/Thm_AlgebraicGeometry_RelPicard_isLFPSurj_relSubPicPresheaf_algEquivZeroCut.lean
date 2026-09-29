-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut
-- name    : AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/c31d687c-3fd3-5fd4-a05b-124ef50e1847
-- title:
--   Classes in relative Pic⁰ descend to f.g. subalgebras
-- statement:
--   Let $R$ be a Noetherian commutative ring and let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume further that $c$ and $\varepsilon$ admit finite-map data of arbitrarily large degree: for every $m_0 \in \mathbb{N}$ there is a datum $\mathfrak{F}$ of type `SmoothProperCurve.FiniteMapData c ε` with $m_0 \le \mathfrak{F}.m$, such a datum consisting of two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ whose basic opens both equal $U \cap V$ and whose restrictions there are mutually inverse, finiteness of $\Gamma(C,U)$ over $R[f]$ and of $\Gamma(C,V)$ over $R[g]$, and, for every local $R$-algebra $S$ and every $s \in S$, freeness and finiteness over $S$ of $S \otimes_R \Gamma(C,U)$ modulo $1 \otimes f - s \otimes 1$ of rank exactly $\mathfrak{F}.m$. The conclusion is `IsLFPSurj` for the subpresheaf `relSubPicPresheaf c ε (algEquivZeroCut c ε)` of the rigidified relative Picard presheaf `relPicardPresheaf c ε` on schemes over $\operatorname{Spec} R$, cut out by the condition that a rigidified line bundle over $t \colon T \to \operatorname{Spec} R$ have, for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to T$, geometric fibre at $s$ algebraically equivalent to zero: namely, for every $R$-algebra $A$ and every element $x$ of this presheaf at $\operatorname{Spec} A$ viewed over $\operatorname{Spec} R$, there are a finitely generated $R$-subalgebra $A_0 \subseteq A$ and an element $x_0$ of the presheaf at $\operatorname{Spec} A_0$ restricting along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ to $x$.
--
--   This is one half of the statement that the relative $\mathrm{Pic}^0$ of a pointed smooth proper curve is locally of finite presentation, in the form of surjectivity of the map from the filtered colimit over finitely generated subalgebras. It is used in the construction of open charts for this subpresheaf and in the proof that a scheme representing it is locally of finite type over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPSurj_relSubPicPresheaf_algEquivZeroCut.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_CategoryTheory_OverTotalPresheaf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  AlgebraicGeometry.AffineLimit

theorem AlgebraicGeometry.RelPicard.isLFPSurj_relSubPicPresheaf_algEquivZeroCut
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPSurj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by sorry
