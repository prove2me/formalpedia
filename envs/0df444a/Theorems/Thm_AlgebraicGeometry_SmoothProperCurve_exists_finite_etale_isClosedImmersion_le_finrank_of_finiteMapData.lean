-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/11bc3ef5-5de5-5cf5-9945-69d8a74ba369
-- title:
--   Large-degree finite étale multisections from finite-map data
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, let $c \colon C \to \operatorname{Spec} R$ be a proper morphism of schemes which is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume that for every $m_0 \in \mathbb{N}$ there is a finite-map datum $\mathfrak{F}$ for $(c,\varepsilon)$ with $m_0 \le \mathfrak{F}.m$ whose level sets are generically étale. Here a finite-map datum consists of affine opens $U, V$ of $C$ with $U \sqcup V = \top$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ and an integer $m$, such that $U$ is exactly the complement of the image of $\varepsilon$, $U \cap V$ equals both the basic open set of $f$ and that of $g$, the restrictions of $f$ and $g$ to $U \cap V$ have product $1$, the $R$-algebra maps $R[T] \to \Gamma(C,U)$, $T \mapsto f$, and $R[T] \to \Gamma(C,V)$, $T \mapsto g$ (for the algebra structures induced by $c$) are finite, and for every local $R$-algebra $S$ and every $s \in S$ the level-set algebra $S \otimes_R \Gamma(C,U) / (1 \otimes f - s \otimes 1)$ is finite and free over $S$ of rank $m$; generic étaleness of the level sets means that there is $D \in R[T]$ having some unit coefficient such that for every local $R$-algebra $S$ with $R \to S$ a local homomorphism and every $s \in S$ with $D(s)$ a unit, that level-set algebra is étale over $S$. Then for every $N \in \mathbb{N}$ there exist a commutative ring $R_0$ which is a local Noetherian $R$-algebra, finite, étale and faithfully flat over $R$, a commutative ring $B$ which is a finite étale $R_0$-algebra, and a morphism $\iota \colon \operatorname{Spec} B \to C \times_{\operatorname{Spec} R} \operatorname{Spec} R_0$ which is a closed immersion, such that $\iota$ followed by the projection $\operatorname{Spec} B \to \operatorname{Spec} R_0$ of the pullback is the structural morphism $\operatorname{Spec} B \to \operatorname{Spec} R_0$, and $N \le \operatorname{rank}_{R_0} B$.
--
--   This produces, after an unramified (finite étale, faithfully flat, local) extension $R_0$ of the discrete valuation ring $R$, a closed subscheme of the base-changed curve $C_{R_0}$ which is finite étale over $R_0$ of degree at least $N$: a finite étale multisection of arbitrarily large degree. It is used in the construction of charts for the relative Picard scheme, via [`AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData`](thm.html#AlgebraicGeometry.RelPicard.exists_finite_etale_hasChartSections_of_finiteMapData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem AlgebraicGeometry.SmoothProperCurve.exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) (N : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ : IsNoetherianRing R₀)
      (B : Type u) (_ : CommRing B) (_ : Algebra R₀ B) (_ : Module.Finite R₀ B) (_ : Algebra.Etale R₀ B)
      (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c R₀ = specMap R₀ B ∧ N ≤ Module.finrank R₀ B := by sorry
