-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_Supplement_lemma_5_2
-- name    : EntropyLocalCoord.Leader.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:20.30031+00:00
-- url     : https://prove2.me/theorems/8c1b09a0-495a-49e6-904a-b118fae9a819
-- title:
--   Lemma 5.2 — $P=2^{-k}\binom{2k-2}{k-1}=\Theta(2^k/\sqrt k)$
-- statement:
--   For an integer $k\ge5$ (the standing assumption of §5), let $P=\sum_{\{f,g\}\in E(H)}p_{fg}$ be the total crossing probability of the graph $H$ of weighted majority functions on $k$ inputs, with $p_{fg}$ computed along an arbitrary coordinate $i$. Then:
--
--   1. for every $k\ge5$ and every coordinate $i$,
--
--   $$P=2^{-k}\binom{2k-2}{k-1};$$
--
--   2. $P=\Theta(2^k/\sqrt k)$: there are absolute constants $c_1,c_2>0$ and a threshold $K_0$ such that for every $k\ge\max(K_0,5)$ and every $i$,
--
--   $$c_1\,\frac{2^k}{\sqrt k}\ \le\ P\ \le\ c_2\,\frac{2^k}{\sqrt k}.$$
--
--   Combined with Lemma 5.1 this converts the cut lower bound into the leader lower bound $\Omega(\sqrt k\,2^{-k})$ of Theorem 3.4.
--
--   Differences from the source:
--   - encoding: p_fg defined along an arbitrary coordinate i, the value being shown on p. 16 not to depend on i → p_fg computed along a coordinate i : Fin k, and the statement asserted for every i; reason: the source's p_fg is the crossing probability along any one coordinate; quantifying over all i states the same claim for every admissible choice and assumes no independence of i
--   - encoding: P = Θ(2^k/√k) as k → ∞ → there are c₁, c₂ > 0 and K₀ with c₁·2^k/√k ≤ P ≤ c₂·2^k/√k for every k ≥ max(K₀, 5); reason: this is the definition of a two-sided Θ bound with absolute constants
--   - encoding: P = ∑_{{f,g}∈E(H)} p_fg → totalCrossing i, one half of the double sum of p_fg over ordered adjacent pairs; reason: each unordered edge appears as two ordered pairs with the same p_fg
--   - encoding: 2^{−k} binom(2k−2, k−1) → (binom(2k−2, k−1) : ℝ) / 2^k with natural-number subtraction; reason: k ≥ 5, so 2k−2 and k−1 are the true differences
--   - encoding: f ∼ g iff the regions of f and g share a facet inside (0,∞)^k → f ∼ g iff f and g disagree exactly on one antipodal pair {x, −x}; reason: the source states this equivalence on p. 14 ("Notice that f ∼ g in H if and only if ..."); the two descriptions give the same graph H
--   - encoding: the path w^(i) crosses the common facet F_fg → some point w^(i)(t), 0 < t ≤ W_i, lies in the set of points of (0,∞)^k in the closures of both regions; reason: for f ∼ g this set is the common facet with its relative boundary; the path is transversal to it, and meeting the relative boundary is a null event, so the probability is the same
--   - encoding: W uniform on Δ = {w ∈ [0,∞)^k : ∑ w_i = 1} → W distributed by the published dirichletOnes k (normalized Lebesgue measure on the corner simplex of ℝ^{k−1} pushed forward by x ↦ (x, 1 − ∑ x_j)); reason: this is the uniform (k−1)-dimensional law on Δ; the affine chart preserves uniformity
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, Lemma 5.2, p. 17 (proof pp. 17–18); standing assumption k ≥ 5, §5 Step 1, p. 13; p_fg, Step 4.1, p. 16.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Supplement_Majority

namespace EntropyLocalCoord.Leader.Supplement

/-- Peretz--Kraizberg, STOC 2027 submission #272, Lemma 5.2, p. 17 (standing assumption `k ≥ 5`
of §5, p. 13). Both clauses: the exact value `P = 2^{-k} binom(2k-2, k-1)` for every `k ≥ 5` and
every coordinate `i` along which `p_fg` is computed, and `P = Θ(2^k / √k)` as `k → ∞`, with
absolute constants `c₁, c₂ > 0`. -/
theorem lemma_5_2 :
    (∀ (k : ℕ), 5 ≤ k → ∀ i : Fin k,
      totalCrossing i = ((Nat.choose (2 * k - 2) (k - 1) : ℕ) : ℝ) / (2 : ℝ) ^ k) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → 5 ≤ k → ∀ i : Fin k,
      c₁ * ((2 : ℝ) ^ k / Real.sqrt k) ≤ totalCrossing i ∧
        totalCrossing i ≤ c₂ * ((2 : ℝ) ^ k / Real.sqrt k) := by sorry

end EntropyLocalCoord.Leader.Supplement
