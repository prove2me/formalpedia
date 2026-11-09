-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_5
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:46.305203+00:00
-- url     : https://prove2.me/theorems/211b0dc5-c322-4932-a99f-61ee924426ce
-- title:
--   Lemma 6.5 — weighted path tail and the hop-count comparison A_j ≤ e²βF_j + O(1)
-- statement:
--   Fix $C>0$ and let $p=j/N$, $\beta=np$. For every $n\ge3$, source $s$, $0\le j\le N$, $t>0$ and $1\le k\le n-1$,
--   $$\Pr_j\bigl(\exists\text{ a simple }k\text{-arc path from }s\text{ of weight at most }t\bigr)\le\frac{(npt/C)^k}{k!}. \tag{11}$$
--   Moreover there are constants $K>0$, $n_0$ such that for $n\ge\max(n_0,3)$, every source and $0\le j\le N$,
--   $$A_j\le e^2\beta F_j+K. \tag{12}$$
--   The factor is $e^2$ times $\beta$.
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: H_x = hop count of the shortest path from s to x (unique almost surely) → H_x = depth of x in the certified shortest-path tree computed by the initialization (Dijkstra) on that graph, 0 if unreachable; reason: shortest paths are unique almost surely, so all expectations and probabilities are unchanged
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.5, equations (11)–(12), PDF p.10 = printed p.10

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.5 (PDF p. 10). For `p = j/N`, `t > 0` and `1 ≤ k ≤ n - 1`,
`Pr_j(∃ a simple k-arc path from s of weight ≤ t) ≤ (n p t / C)^k / k!` (11). Moreover, with
`β = n p`, `A_j ≤ e² β F_j + O(1)` (12). -/
theorem lemma_6_5 (C : ℝ) (hC : 0 < C) :
    (∀ n : ℕ, 3 ≤ n → ∀ (s : Fin n) (j : ℕ), j ≤ numPairs n → ∀ t : ℝ, 0 < t →
      ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
        gnm n C j {g | ∃ l : List (Fin n), l.Nodup ∧ g.graph.IsWalk l ∧ l.head? = some s ∧
            WDigraph.hops l = k ∧ g.graph.walkWeight l ≤ ENNReal.ofReal t} ≤
          ENNReal.ofReal ((n * ((j : ℝ) / numPairs n) * t / C) ^ k / (k.factorial : ℝ))) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n → ∀ (s : Fin n) (j : ℕ),
      j ≤ numPairs n →
        totalHop n C s j ≤
          ENNReal.ofReal (Real.exp 2 * (n * ((j : ℝ) / numPairs n))) * totalUdist n C s j +
            ENNReal.ofReal K) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
