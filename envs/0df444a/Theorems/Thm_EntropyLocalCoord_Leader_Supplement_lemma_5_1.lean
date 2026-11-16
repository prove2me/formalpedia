-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_Supplement_lemma_5_1
-- name    : EntropyLocalCoord.Leader.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:47.877084+00:00
-- url     : https://prove2.me/theorems/b7497d92-4623-47e0-8cad-4055177d37a0
-- title:
--   Lemma 5.1 — crossing-weighted total variation of supported measures is at least $\tfrac12$
-- statement:
--   Fix an integer $k\ge5$ (the standing assumption of §5) and let $H$ be the graph of positive-weight, tie-free weighted majority functions on $k$ inputs, with crossing probabilities $p_{fg}$ computed along an arbitrary coordinate $i\in[k]$.
--
--   For each $f\in V(H)$ let $\mu_f$ be a probability measure on $\operatorname{supp}(f)$, extended by zero to $[k]$. Then
--
--   $$\sum_{\{f,g\}\in E(H)}p_{fg}\,\|\mu_f-\mu_g\|_{\mathrm{TV}}\ \ge\ \frac12,$$
--
--   where $\|\nu\|_{\mathrm{TV}}=\frac12\sum_{j=1}^k|\nu(j)|$ and each edge of $H$ is counted once.
--
--   The measures are arbitrary: in the proof of Theorem 3.4 they are the empirical laws of the coordinates assigned to the copies of each function, and the inequality bounds the expected number of cut edges from below.
--
--   Differences from the source:
--   - encoding: p_fg defined along an arbitrary coordinate i, the value being shown on p. 16 not to depend on i → p_fg computed along a coordinate i : Fin k, and the statement asserted for every i; reason: the source's p_fg is the crossing probability along any one coordinate; quantifying over all i states the same claim for every admissible choice and assumes no independence of i
--   - encoding: μ_f a probability measure on supp(f) → μ_f : Fin k → ℝ, nonnegative, summing to 1, and vanishing off supp(f); reason: a probability measure on a finite set is its mass vector; the zero extension to [k] is the one the source uses in ‖μ_f − μ_g‖_TV
--   - encoding: sum over unordered edges {f,g} ∈ E(H), each once → one half of the double sum over ordered pairs (f,g) with f ∼ g; reason: each unordered edge appears as two ordered pairs with the same summand (p_fg and ‖μ_f − μ_g‖_TV are symmetric)
--   - encoding: f ∼ g iff the regions of f and g share a facet inside (0,∞)^k → f ∼ g iff f and g disagree exactly on one antipodal pair {x, −x}; reason: the source states this equivalence on p. 14 ("Notice that f ∼ g in H if and only if ..."); the two descriptions give the same graph H
--   - encoding: the path w^(i) crosses the common facet F_fg → some point w^(i)(t), 0 < t ≤ W_i, lies in the set of points of (0,∞)^k in the closures of both regions; reason: for f ∼ g this set is the common facet with its relative boundary; the path is transversal to it, and meeting the relative boundary is a null event, so the probability is the same
--   - encoding: W uniform on Δ = {w ∈ [0,∞)^k : ∑ w_i = 1} → W distributed by the published dirichletOnes k (normalized Lebesgue measure on the corner simplex of ℝ^{k−1} pushed forward by x ↦ (x, 1 − ∑ x_j)); reason: this is the uniform (k−1)-dimensional law on Δ; the affine chart preserves uniformity
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, Lemma 5.1, p. 16 (proof p. 17); standing assumption k ≥ 5, §5 Step 1, p. 13; p_fg, Step 4.1, p. 16.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Information
import Definitions.Def_EntropyLocalCoord_Leader_Supplement_Majority

open scoped Classical

namespace EntropyLocalCoord.Leader.Supplement

/-- Peretz--Kraizberg, STOC 2027 submission #272, Lemma 5.1, p. 16 (standing assumption `k ≥ 5`
of §5, p. 13). For every family `(μ_f)_{f ∈ V(H)}` of probability vectors on `[k]` with `μ_f`
supported on `supp(f)`, `∑_{{f,g} ∈ E(H)} p_fg ‖μ_f − μ_g‖_TV ≥ 1/2`; `p_fg` is computed along an
arbitrary coordinate `i`, and each unordered edge is counted once (ordered pairs, halved). -/
theorem lemma_5_1 (k : ℕ) (hk : 5 ≤ k) (i : Fin k) (μ : MajFun k → Fin k → ℝ)
    (hμ_nonneg : ∀ f j, 0 ≤ μ f j) (hμ_sum : ∀ f, ∑ j, μ f j = 1)
    (hμ_supp : ∀ f j, j ∉ supp f.1 → μ f j = 0) :
    1 / 2 ≤ (1 / 2) * ∑ f : MajFun k, ∑ g : MajFun k,
      if (auxGraph k).Adj f g then crossProb i f.1 g.1 * tvNorm (μ f - μ g) else 0 := by sorry

end EntropyLocalCoord.Leader.Supplement
