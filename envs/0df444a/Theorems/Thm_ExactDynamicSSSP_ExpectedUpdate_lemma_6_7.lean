-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_7
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:38:56.323605+00:00
-- url     : https://prove2.me/theorems/0e9c9edf-77ad-4f5c-99f5-5740762c3a4e
-- title:
--   Lemma 6.7 — finite-distance tail in the critical window
-- statement:
--   Fix $C>0$ and $a\ge0$. There is a constant $b_a>0$ such that for every $n\ge3$, every source $s$ and every $j$ with $n/2\le j\le n+an^{2/3}$ (and $j\le N$), the largest finite unweighted distance $\mathcal R_s$ from $s$ satisfies
--   $$\Pr_j\bigl(\mathcal R_s>b_a\,n^{1/3}(\log n)^{2/3}\bigr)\le n^{-30}.$$
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: 'for a sufficiently large constant b_a', uniformly in the interval → ∃ b > 0 such that the bound holds for every n ≥ 3 and every j in the interval; reason: the exact tail n^{-30} is kept; small n are absorbed by b because ℛ_s ≤ n − 1
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.7, PDF p.11 = printed p.11

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.7 (PDF p. 11). Fix `a ≥ 0`. For a sufficiently large constant `b_a`, uniformly for
`n/2 ≤ j ≤ n + a n^{2/3}`, the largest finite unweighted distance `ℛ_s` from `s` satisfies
`Pr_j(ℛ_s > b_a n^{1/3} (log n)^{2/3}) ≤ n^{-30}`. -/
theorem lemma_6_7 (C : ℝ) (hC : 0 < C) (a : ℝ) (ha : 0 ≤ a) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, 3 ≤ n → ∀ (s : Fin n) (j : ℕ),
      (n : ℝ) / 2 ≤ j → (j : ℝ) ≤ n + a * (n : ℝ) ^ ((2 : ℝ) / 3) → j ≤ numPairs n →
        gnm n C j {g | b * (n : ℝ) ^ ((1 : ℝ) / 3) * Real.log n ^ ((2 : ℝ) / 3) <
            (maxFinDist s g : ℝ)} ≤ ENNReal.ofReal ((n : ℝ) ^ (-30 : ℝ)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
