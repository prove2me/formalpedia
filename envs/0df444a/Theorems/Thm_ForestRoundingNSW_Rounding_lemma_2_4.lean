-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_lemma_2_4
-- name    : ForestRoundingNSW.Rounding.lemma_2_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:50:25.037848+00:00
-- url     : https://prove2.me/theorems/3e63cc9c-04cb-45a6-8238-2e5732508f36
-- title:
--   Lemma 2.4 — ∂_j F ≥ 0, ∂_jj F = 0, ∂_jk F ≤ 0, and F is convex along a e_j − b e_k
-- statement:
--   Let $f:2^X\to\mathbb R_{\ge0}$ be normalized, monotone and submodular with multilinear extension $F$, and let $z\in[0,1]^X$.
--
--   (2.4a) For every $j$, $\partial_jF(z)\ge0$ and $\partial_{jj}F(z)=0$; for distinct $j,k$, $\partial_{jk}F(z)\le0$.
--
--   (2.4b) For distinct $j,k$ and $a,b\ge0$, let $d=ae_j-be_k$. The function $t\mapsto F(z+td)$ is convex on the interval $I=\{t: z+td\in[0,1]^X\}$; in particular, if $\nabla F(z)\cdot d=0$, then
--   $$F(z+td)\ge F(z)\qquad\text{for every }t\in I.$$
--
--   These are the properties of [CCPV11] that make the balanced moves of Algorithm 1 and the cycle elimination of Lemma 3.1 value-preserving.
--
--   Differences from the source:
--   - encoding: f : 2^M → ℝ≥0 normalized monotone submodular → f : Finset X → ℝ with IsNMS f; reason: nonnegativity follows from normalized and monotone
--   - encoding: ∂_jj F, ∂_jk F → iterated partial derivatives ∂_j(∂_j F) and ∂_j(∂_k F) of the polynomial F; reason: Lean convention; F is a polynomial, so the order does not matter
--   - reading: the interval where z + td ∈ [0,1]^M → the set {t ∈ ℝ : z + t d ∈ [0,1]^X}, with ConvexOn on that set and the minimum clause for every t in it; reason: the literal set named by the source
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 14, Lemma 2.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions

open NonmonotoneSubmod.Shared

namespace ForestRoundingNSW.Rounding

theorem lemma_2_4 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (hf : IsNMS f)
    (z : X → ℝ) (hz : InUnitCube z) :
    ((∀ j : X, 0 ≤ partialDeriv (F f) j z ∧ partialDeriv (partialDeriv (F f) j) j z = 0) ∧
      ∀ j k : X, j ≠ k → partialDeriv (partialDeriv (F f) k) j z ≤ 0) ∧
    ∀ j k : X, j ≠ k → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      ConvexOn ℝ {t : ℝ | InUnitCube (z + t • (a • Pi.single j (1 : ℝ) - b • Pi.single k (1 : ℝ)))}
          (fun t => F f (z + t • (a • Pi.single j (1 : ℝ) - b • Pi.single k (1 : ℝ)))) ∧
      (gradDot (F f) z (a • Pi.single j (1 : ℝ) - b • Pi.single k (1 : ℝ)) = 0 →
        ∀ t : ℝ, InUnitCube (z + t • (a • Pi.single j (1 : ℝ) - b • Pi.single k (1 : ℝ))) →
          F f z ≤ F f (z + t • (a • Pi.single j (1 : ℝ) - b • Pi.single k (1 : ℝ)))) := by sorry

end ForestRoundingNSW.Rounding
