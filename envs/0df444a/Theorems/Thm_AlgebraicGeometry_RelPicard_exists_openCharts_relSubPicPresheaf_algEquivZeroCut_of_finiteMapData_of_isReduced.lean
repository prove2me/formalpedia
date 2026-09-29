-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced
-- name    : AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/431b3a94-1bfb-5d89-afcd-52dead87227d
-- title:
--   Open charts cover relative Pic⁰ over a reduced base
-- statement:
--   Let $R$ be a reduced Noetherian commutative ring, let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is, a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume `h𝔉`: for every $m_0$ there is a `SmoothProperCurve.FiniteMapData` for $(c,\varepsilon)$ of degree $\mathfrak{F}.m \ge m_0$, i.e. two affine opens $U, V$ with $U \sqcup V = C$, $U$ exactly the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ whose restrictions to $U \cap V = C_f = C_g$ are mutually inverse, with $R[f] \to \Gamma(C,U)$ and $R[g] \to \Gamma(C,V)$ finite and, for every local $R$-algebra $S$ and every $s \in S$, the level ring $S \otimes_R \Gamma(C,U)/(1 \otimes f - s \otimes 1)$ free of rank $\mathfrak{F}.m$ over $S$. Let $n, g, r$ be natural numbers with $2g < r$, and let $\gamma$ be an $n$-indexed family of $(r-g)$-tuples of sections of $c$ satisfying `HasChartSections c γ`: over every algebraically closed field $k$ and every $k$-point $s$ of $\operatorname{Spec} R$ there are a field $L$ over $k$, a `CurveModel` $M$ for $(k,L)$ and an isomorphism $M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ over $\operatorname{Spec} k$ for which a Riemann–Roch formula with the given $g$ holds and every effective divisor $D$ of degree $r$ satisfies $\ell\bigl(D - \sum_j (\gamma_{i j})_s\bigr) = 1$ for some index $i$. The conclusion: there exist schemes $X_i$ indexed by $\mathrm{ULift}(\mathrm{Fin}\,n)$ and morphisms $f_i$ from the (universe-lifted) functor of points of $X_i$ to the total presheaf $T \mapsto \coprod_{t \colon T \to \operatorname{Spec} R} (\mathtt{relSubPicPresheaf}\,c\,\varepsilon\,(\mathtt{algEquivZeroCut}\,c\,\varepsilon))(T,t)$ — the subpresheaf of the rigidified relative Picard presheaf consisting of classes of rigidified line bundles whose pullback to every geometric fibre is algebraically equivalent to zero — such that each $f_i$ is relatively representable by open immersions in the sense of `MorphismProperty.presheafULift @IsOpenImmersion`, and the induced morphism out of $\coprod_i X_i$ is locally surjective for the Zariski topology on schemes.
--
--   This is the chart-construction step towards representability of the relative $\mathrm{Pic}^0$ of a pointed smooth proper curve by a scheme: Milne's charts, indexed by the $n$ tuples of sections, form an open covering family of the total presheaf. It is the variant over a reduced Noetherian base, where the Zariski sheaf property of the subpresheaf is available, and it feeds the representability theorem [`AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced`](thm.html#AlgebraicGeometry.RelPicard.exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced.lean

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

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.RelPicard.exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ) :
    ∃ (X : ULift.{u} (Fin n) → Scheme.{u})
      (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε (algEquivZeroCut c ε)).overTotal),
      (∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i)) ∧
        Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f) := by sorry
