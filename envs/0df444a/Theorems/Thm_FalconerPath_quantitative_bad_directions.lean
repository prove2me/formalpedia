-- Prove2me | Theorems.Thm_FalconerPath_quantitative_bad_directions
-- name    : FalconerPath.quantitative_bad_directions
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:55.285437+00:00
-- url     : https://prove2.me/theorems/1dcbf7a4-7319-4bef-a41b-8f050f39faa9
-- title:
--   A common Borel envelope for bad tube directions
-- statement:
--   Fix $k\ge2$, $k-1\le q\le k-\tfrac12$, $k-\tfrac12<t<k$, and $\zeta,L,C>0$. There are $c_1,\varepsilon_1>0$ and $0<\delta_0\le1$ such that for every $0<\delta\le\delta_0$ and every probability $\mu$ carried by $\overline B(0,L)$ with $\mu(B(z,r))\le\delta^{-\varepsilon_1}r^t$ for all centers and $\delta\le r\le1$, the following holds. Let $B_\delta$ be the unit directions for which a union of at most $\delta^{-q-c_1}$ radius-$C\delta$ tubes parallel to that direction, truncated to $\overline B(0,L)$, has $\mu$-mass at least $\delta^{c_1}$.
--
--   There is a Borel $B_\delta^+\subset S^k$ containing $B_\delta$, chosen before the direction law, such that every subprobability $\lambda$ carried by $S^k$ satisfies $\lambda(B_\delta^+)\le\delta^{c_1}$ provided its caps have mass at most $\delta^{-\varepsilon_1}u^q$ for $\delta\le u\le1$ and, when $q=k-1$, every width-$u$ directional plate has mass at most $\delta^{-\varepsilon_1}u^\zeta$ for those radii. The Lean formulation expands the inherited parameter conditions and the uniform choice of the Borel envelope.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 4.5, Corollary 4.8 (Small mass of bad directions), label ang:bad-directions, with parameters inherited from Theorem 4.1 (Linear projection gain), label ang:linear-gain, including the endpoint plate condition labeled ang:endpoint-plate.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem quantitative_bad_directions {k : ℕ} (hk : 2 ≤ k) (q t ζ L C : ℝ)
    (hq : (k:ℝ)-1 ≤ q) (hqS : q ≤ (k:ℝ)-1/2)
    (ht : (k:ℝ)-1/2 < t) (htk : t < k)
    (hζ : 0 < ζ) (hL : 0 < L) (hC : 0 < C) :
    ∃ c₁ ε₁ δ₀ : ℝ, 0 < c₁ ∧ 0 < ε₁ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ μ : Measure (Space (k+1)),
        Probability μ → Carried μ (Metric.closedBall 0 L) →
        ballBound μ t (δ^(-ε₁)) δ →
        ∃ Bplus : Set (Space (k+1)), MeasurableSet Bplus ∧ Bplus ⊆ unitSphere (k+1) ∧
          badDirections μ L C δ q c₁ ⊆ Bplus ∧
          ∀ lam : Measure (Space (k+1)), Subprobability lam →
            Carried lam (unitSphere (k+1)) → capBound lam q (δ^(-ε₁)) δ →
            (q = (k:ℝ)-1 → plateBound lam ζ (δ^(-ε₁)) δ) →
            lam Bplus ≤ ENNReal.ofReal (δ^c₁) := by sorry
end FalconerPath
