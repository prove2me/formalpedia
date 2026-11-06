-- Prove2me | Theorems.Thm_FalconerPath_direction_law_on_sphere
-- name    : FalconerPath.direction_law_on_sphere
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:55.818033+00:00
-- url     : https://prove2.me/theorems/99df3051-6bae-4df4-a648-282aef6a7e40
-- title:
--   Transport of an ambient direction law to the unit sphere
-- statement:
--   Let $k\in\mathbb N$ with $k\ge2$ and $q,\zeta,K,\delta\in\mathbb R$ with $\delta>0$. Let $\lambda$ be an ambient measure of total mass at most one carried by $S^k$. Write $[u]_+=\max(u,0)$ in the extended nonnegative reals. Assume $\lambda(B(w,r))\le[Kr^q]_+$ for every $w\in S^k$ and $\delta\le r\le1$. If $q=k-1$, assume also $\lambda\{w\in S^k:|\langle w,v\rangle|\le r\}\le[Kr^\zeta]_+$ for every unit vector $v$ and $\delta\le r\le1$. There exists a measure $\nu$ on the metric sphere $S^k$ with $\nu(S^k)\le1$ satisfying $\nu(B_{S^k}(w,r))\le[Kr^q]_+$ for every $w\in S^k$ and $\delta\le r\le1$. If $q=k-1$, then for every $k$-dimensional linear subspace $H\subseteq\mathbb R^{k+1}$ and $\delta\le r\le1$, $\nu\{w\in S^k:\operatorname{dist}(w,H)\le r\}\le[Kr^\zeta]_+$. For every ambient Borel set $B\subseteq S^k$, $\nu(\{w\in S^k:w\in B\})=\lambda(B)$.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 4, Theorem 4.1 (ang:linear-gain) and Corollary 4.8 (ang:bad-directions), the direction-law convention and distance-to-hyperplane condition (ang:endpoint-plate) in Theorem 4.1, together with the final invocation of Theorem 4.1 in the proof paragraph of Corollary 4.8. This supplies the ambient-to-sphere representation change without normalizing the law.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 4, proof of Corollary 4.8: regard the unchanged direction
subprobability as a law on S^k when invoking Theorem 4.1. The unit-normal
plate formulation agrees with distance to a codimension-one subspace. -/
theorem direction_law_on_sphere {k : ℕ} (hk : 2 ≤ k)
    (lam : Measure (Space (k+1))) (q ζ K δ : ℝ) (hδ : 0 < δ)
    (hlam : Subprobability lam) (hcar : Carried lam (unitSphere (k+1)))
    (hcap : capBound lam q K δ)
    (hplate : q = (k:ℝ)-1 → plateBound lam ζ K δ) :
    ∃ ν : Measure (Metric.sphere (0 : Space (k+1)) 1),
      ν univ ≤ 1 ∧
      (∀ w : Metric.sphere (0 : Space (k+1)) 1, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ν (Metric.ball w r) ≤ ENNReal.ofReal (K*r^q)) ∧
      (q = (k:ℝ)-1 → ∀ H : Submodule ℝ (Space (k+1)),
        Module.finrank ℝ H = k → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
          ν {w | Metric.infDist (w : Space (k+1)) (H : Set _) ≤ r} ≤
            ENNReal.ofReal (K*r^ζ)) ∧
      ∀ B : Set (Space (k+1)), MeasurableSet B → B ⊆ unitSphere (k+1) →
        ν (Subtype.val ⁻¹' B) = lam B := by sorry
end FalconerPath
