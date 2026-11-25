-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_embeddedHoloDisk_near_elliptic
-- name    : FiniteEnergyPlane.exists_embeddedHoloDisk_near_elliptic
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:36:49.828278+00:00
-- url     : https://prove2.me/theorems/d3b5fcfa-5259-5a11-bfcd-522b2b815ad5
-- title:
--   Embedded pseudoholomorphic disks near a nicely elliptic point, for an open set of $J$
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with Reeb field $R$ and contact planes $\xi$. Let $P=(x,T)$ be a periodic Reeb orbit and $e$ a special spanning disk for $P$ with singular point $e(z_0)$. Suppose the positive area of $e$ satisfies $\int_{\mathring D}\max(\omega_0(\partial_se,\partial_te),0)<C$, and let $U$ be a neighbourhood of $z_0$. Then there are
--
--   1. a special spanning disk $e'$ for $P$ with singular point $e'(z_0)=e(z_0)$, equal to $e$ off $U$, of positive area less than $C$;
--   2. a compatible $J_0$, an integer $k\ge0$ and $\varepsilon>0$, such that for every compatible $J$
--   $$\|J-J_0\|_{C^k(S)}\le\varepsilon\ \Longrightarrow\ \text{there is an embedded }\tilde J\text{-holomorphic disk }u$$
--   with boundary loop in $e'(\mathring D)$, of winding number $1$ around $e'(z_0)$, whose projection to $S$ is disjoint from $x(\mathbb{R})$.
--
--   Here $\mathring D$ is the open unit disk. The statement provides embedded disks for all complex structures in a $C^k$-open set, with control on the spanning disk away from its singular point.
--
--   **Formalization Note** Closeness in $C^k$ on $S$ is `IsXiClose H k ε J J₀`. The terms special spanning disk, disk curve and embedded holomorphic disk are `IsSpecialSpanningDisk`, `IsDiskCurve` and `IsEmbeddedHoloDisk` of `FiniteEnergyPlane_SpanningDisk`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, Lemma 3.5 and the paragraph preceding it; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 36

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hryniewicz (2014), Lemma 3.5 and the paragraph preceding it; Hofer (1993), Theorem 36. Let `e` be a special
spanning disk for `P` with singular point `e z₀` and positive area less than `C`, and let `U` be a
neighbourhood of `z₀`. There are a special spanning disk `e'` with the same singular point, equal to `e` off
`U` and of positive area less than `C`, a compatible `J₀`, and `k, ε > 0`, such that for every compatible
`J` that is `ε`-close to `J₀` in `C^k` there is an embedded `J̃`-holomorphic disk with boundary on `e'`, winding
once around the singular point and disjoint from `ℝ × x(ℝ)`. -/
theorem exists_embeddedHoloDisk_near_elliptic (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) (he : IsSpecialSpanningDisk H P e z₀)
    (C : ℝ) (hC : diskArea e < ENNReal.ofReal C) (U : Set ℂ) (hU : U ∈ 𝓝 z₀) :
    ∃ e' : ℂ → V 1, IsSpecialSpanningDisk H P e' z₀ ∧ e' z₀ = e z₀ ∧ (∀ z ∉ U, e' z = e z) ∧
      diskArea e' < ENNReal.ofReal C ∧
      ∃ J₀ : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J₀ ∧ ∃ (k : ℕ) (ε : ℝ), 0 < ε ∧
        ∀ J : V 1 → V 1 →L[ℝ] V 1, IsCompatibleXiStructure H J → IsXiClose H k ε J J₀ →
          ∃ u : ℂ → V 1, IsEmbeddedHoloDisk H J e' z₀ (ball 0 1) u ∧
            ∀ z ∈ closedBall (0 : ℂ) 1, proj H (u z) ∉ Set.range P.x := by
  sorry

end FiniteEnergyPlane
