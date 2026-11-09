-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_8
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:06.175208+00:00
-- url     : https://prove2.me/theorems/ef5911a4-d937-4419-a556-27cddc14093a
-- title:
--   Lemma 6.8 — short finite distances in supercritical random digraphs
-- statement:
--   Fix $C>0$ and $\varepsilon,K>0$. There are constants $b_{\varepsilon,K}>0$, $c>0$ and $n_0$ such that for $n\ge\max(n_0,3)$ and every $j$ with $(1+\varepsilon)n\le j\le Kn\log n$ (and $j\le N$), with probability at least $1-c\,n^{-20}$ under $\mathcal G_{n,j}$ every reachable ordered pair $(x,y)$ is joined by an unweighted directed path of length at most $b_{\varepsilon,K}\log n$:
--   $$\Pr_j\bigl(\exists\,x,y:\ y\text{ reachable from }x,\ \mathrm{udist}(x,y)>b_{\varepsilon,K}\log n\bigr)\le c\,n^{-20}.$$
--   No strong connectivity is asserted.
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.8, PDF p.11 = printed p.11; full proof Appendix C, PDF pp.16–17

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.8 (PDF p. 11; proof Appendix C, pp. 16–17). Fix `ε, K > 0`. If
`(1 + ε) n ≤ j ≤ K n log n`, then with probability `1 - O_{ε,K}(n^{-20})` every reachable ordered
pair is joined by an unweighted directed path of length at most `b_{ε,K} log n`. -/
theorem lemma_6_8 (C : ℝ) (hC : 0 < C) (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    ∃ b c : ℝ, 0 < b ∧ 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n → ∀ j : ℕ,
      (1 + ε) * n ≤ j → (j : ℝ) ≤ K * n * Real.log n → j ≤ numPairs n →
        gnm n C j {g | ∃ x y : Fin n, g.graph.Reach x y ∧
            b * Real.log n < (g.graph.udist x y : ℝ)} ≤
          ENNReal.ofReal (c * (n : ℝ) ^ (-20 : ℝ)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
