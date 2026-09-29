-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData
-- name    : AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/d1c3b230-8605-54ea-856e-31a3f19b3942
-- title:
--   Chart sections after a finite étale extension of a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), let $c \colon C \to \operatorname{Spec} R$ be proper, smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Assume that for every $m_0 \in \mathbb{N}$ there is a `FiniteMapData` datum $\mathfrak{F}$ for $(c,\varepsilon)$ — a pair of affine opens $U, V$ covering $C$ with $U$ the complement of the image of $\varepsilon$, functions $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ cutting out $U \cap V$ as a common basic open and mutually inverse there, each finite over the polynomial algebra, together with a degree $m$ such that every level set $S \otimes_R \Gamma(C,U)/(1\otimes f - s\otimes 1)$ over a local $R$-algebra $S$ is finite free of rank $m$ — with $m_0 \le \mathfrak{F}.m$ and satisfying `LevelSetsGenericallyEtale`: some polynomial $D \in R[X]$ with a unit coefficient is such that, over any local $R$-algebra $S$ with local structure map and any $s \in S$ with $D(s)$ a unit, the level set at $s$ is étale over $S$. Then there exist a finite étale faithfully flat Noetherian $R$-algebra $R'$ and natural numbers $n, g, r$ with $2g < r$, together with a family $\gamma \colon \mathrm{Fin}\,n \to \mathrm{Fin}(r-g) \to$ sections of the base change $C_{R'} \to \operatorname{Spec} R'$, such that `HasChartSections` holds: for every algebraically closed field $k$ and every $\operatorname{Spec} k \to \operatorname{Spec} R'$ there are a field extension $L/k$ and a curve model $M$ over $(k,L)$ with an isomorphism $e$ of $M.C$ with the fibre $C_{R'} \times_{\operatorname{Spec} R'} \operatorname{Spec} k$ compatible with the projections, for which Riemann–Roch holds on $L$ with some canonical divisor $K_c$ and this genus $g$, and for every effective divisor $D$ on $L$ of degree $r$ there is an index $i$ with $\ell\bigl(D - \sum_{j} [\gamma_{i,j}(\bar s)]\bigr) = 1$, the places being those attached through $M$ to the fibre points of the sections $\gamma_{i,j}$.
--
--   This is the supply of chart data for Milne's construction of the relative Jacobian of a smooth proper curve over a discrete valuation ring: after a finite étale base change one has finitely many tuples of sections that, on every geometric fibre, cut every effective divisor of degree $r > 2g$ down to a one-dimensional Riemann–Roch space. It is used in the construction of the relative Jacobian and in the representability statement for the associated relative sub-Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_finite_etale_hasChartSections_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra

theorem AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Module.Finite R R')
      (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R') (_ : IsNoetherianRing R')
      (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R')),
      HasChartSections (baseChange R c R') γ := by sorry
