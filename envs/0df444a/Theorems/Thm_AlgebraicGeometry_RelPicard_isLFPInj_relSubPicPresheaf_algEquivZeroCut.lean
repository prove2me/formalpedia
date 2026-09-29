-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut
-- name    : AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/02165339-9371-5ad2-96b0-2e8485d465d0
-- title:
--   Injectivity half of local finite presentation for Pic⁰
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume further that finite map data for $(c,\varepsilon)$ exist with arbitrarily large invariant $m$: for every $m_0 \in \mathbb{N}$ there is a `SmoothProperCurve.FiniteMapData c ε` with $m_0 \le m$, such data consisting of two affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ whose basic open sets both equal $U \cap V$ and which are mutually inverse there, finiteness of $\Gamma(C,U)$ over $R[f]$ and of $\Gamma(C,V)$ over $R[g]$, and freeness of rank $m$ of every level set of $f$ over a local $R$-algebra. The conclusion is the predicate `IsLFPInj` for the subpresheaf of `relPicardPresheaf c ε` on $(\mathrm{Over}\ \operatorname{Spec} R)^{\mathrm{op}}$ cut out by the condition `algEquivZeroCut c ε`, namely that a rigidified line bundle over $t \colon T \to \operatorname{Spec} R$ be fibrewise algebraically equivalent to zero, i.e. `IsAlgEquivZero` holds for its pullback to the fibre at every point $\operatorname{Spec} k \to T$ with $k$ algebraically closed. Explicitly: for every $R$-algebra $A$, every finitely generated $R$-subalgebra $A_0 \subseteq A$ and all $x_0, x_0'$ in the value of this subpresheaf at $\operatorname{Spec} A_0$ over $\operatorname{Spec} R$, if the restrictions of $x_0$ and $x_0'$ along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ agree, then there is a finitely generated $R$-subalgebra $A_1$ with $A_0 \le A_1 \subseteq A$ such that the restrictions of $x_0$ and $x_0'$ along $\operatorname{Spec} A_1 \to \operatorname{Spec} A_0$ already agree.
--
--   This is the injectivity half of the statement that the relative Picard functor $\mathrm{Pic}^0_{C/R,\varepsilon}$ of a pointed smooth proper curve is locally of finite presentation, in the form of Bosch–Lütkebohmert–Raynaud 8.1 and EGA IV 8.5.2. Together with the corresponding surjectivity statement it is used to extend the open charts of the relative Jacobian to arbitrary test schemes, and it is cited for that purpose by [`AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut.lean

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

theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by sorry
