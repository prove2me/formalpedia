-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_4
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:35.547285+00:00
-- url     : https://prove2.me/theorems/96284b03-725b-4e04-9704-8da10df615a8
-- title:
--   Lemma 6.4 — degree-weighted depths versus A_{j−1}
-- statement:
--   Fix $C>0$ and let $\kappa_j=(1-(j-1)/N)^{-1}$. For every $n\ge3$, every source and $1\le j\le N$,
--   $$\mathbb E_j\sum_xD^+_xH_x\le\kappa_j\,\frac jn\,A_{j-1},\qquad \mathbb E_j\sum_xD^-_xH_x\le\kappa_j\Bigl(\frac{2j}{n}A_{j-1}+j\Bigr). \tag{9}$$
--   In particular, for $j=O(n)$: for every fixed $c>0$ there are $K>0$ and $n_0$ such that for $n\ge\max(n_0,3)$, every source and $1\le j\le\min(cn,N)$,
--   $$\mathcal C_{n,j}\le K\Bigl(1+\frac{A_{j-1}}n+\frac{\log n}{j}A_j\Bigr). \tag{10}$$
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: H_x = hop count of the shortest path from s to x (unique almost surely) → H_x = depth of x in the certified shortest-path tree computed by the initialization (Dijkstra) on that graph, 0 if unreachable; reason: shortest paths are unique almost surely, so all expectations and probabilities are unchanged
--   - encoding: (10) 'for j = O(n)' → for every fixed c > 0, a constant K and threshold n₀ valid for all 1 ≤ j ≤ c·n; reason: standard meaning of j = O(n) with a constant uniform for each fixed ratio
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.4, equations (9)–(10), PDF p.9 = printed p.9

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.4 (PDF p. 9). With `κ_j = (1 - (j-1)/N)^{-1}`, for `1 ≤ j ≤ N`:
`𝔼_j Σ_x D⁺_x H_x ≤ κ_j (j/n) A_{j-1}` and `𝔼_j Σ_x D⁻_x H_x ≤ κ_j ((2j/n) A_{j-1} + j)` (9).
In particular, for `j = O(n)` (any fixed ratio `j ≤ c n`),
`𝒞_{n,j} = O(1 + A_{j-1}/n + (log n / j) A_j)` (10). -/
theorem lemma_6_4 (C : ℝ) (hC : 0 < C) :
    (∀ n : ℕ, 3 ≤ n → ∀ (s : Fin n) (j : ℕ), 1 ≤ j → j ≤ numPairs n →
      ∫⁻ g, ∑ x, (g.graph.outDeg x : ℝ≥0∞) * (hop s g x : ℝ≥0∞) ∂(gnm n C j) ≤
          ENNReal.ofReal ((1 - ((j : ℝ) - 1) / numPairs n)⁻¹ * (j / n)) *
            totalHop n C s (j - 1) ∧
      ∫⁻ g, ∑ x, (g.graph.inDeg x : ℝ≥0∞) * (hop s g x : ℝ≥0∞) ∂(gnm n C j) ≤
          ENNReal.ofReal ((1 - ((j : ℝ) - 1) / numPairs n)⁻¹) *
            (ENNReal.ofReal (2 * j / n) * totalHop n C s (j - 1) + (j : ℝ≥0∞))) ∧
    (∀ c : ℝ, 0 < c → ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n →
      ∀ (s : Fin n) (j : ℕ), 1 ≤ j → (j : ℝ) ≤ c * n → j ≤ numPairs n →
        costFunctional n C s j ≤
          ENNReal.ofReal K * (1 + totalHop n C s (j - 1) / (n : ℝ≥0∞) +
            ENNReal.ofReal (Real.log n / j) * totalHop n C s j)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
