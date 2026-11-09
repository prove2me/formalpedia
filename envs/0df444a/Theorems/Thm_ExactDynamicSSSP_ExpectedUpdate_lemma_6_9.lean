-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_lemma_6_9
-- name    : ExactDynamicSSSP.ExpectedUpdate.lemma_6_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:05.119577+00:00
-- url     : https://prove2.me/theorems/23f558ba-ed03-4cf5-ab4b-47e38a704113
-- title:
--   Lemma 6.9 — light-arc paths in dense random digraphs
-- statement:
--   Fix $C>0$. For $j\ge512\,n\log n$ put
--   $$\theta=\frac{512\,n\log n}{j},\qquad L_n=2\lceil\log_2n\rceil+1,\qquad t_n=C\theta L_n, \tag{21}$$
--   and call an arc light if its weight is at most $C\theta$. There are constants $c>0$, $n_0$ such that for $n\ge\max(n_0,3)$ and every $512\,n\log n\le j\le N$:
--
--   1. with probability at least $1-c\,n^{-20}$, every ordered pair $(x,y)$ is connected by a path of at most $L_n$ light arcs;
--   2. consequently, on this event all weighted distances are at most $t_n$: $d(x,y)\le t_n$ for all $x,y$.
--
--   Differences from the source:
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - encoding: a path of at most L_n light arcs → a walk with at most L_n arcs, all light; reason: deleting cycles from such a walk gives a path with at most L_n light arcs
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Lemma 6.9 with the preamble (21), PDF p.12 = printed p.12

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Lemma 6.9 (PDF p. 12). Let `j ≥ 512 n log n`, `θ = 512 n log n / j`,
`L_n = 2⌈log₂ n⌉ + 1`, `t_n = C θ L_n` (21), and call an arc light if its weight is at most
`C θ`. With probability `1 - O(n^{-20})` every ordered pair is connected by a path of at most
`L_n` light arcs; consequently all weighted distances are at most `t_n` on this event. -/
theorem lemma_6_9 (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n → ∀ j : ℕ,
      512 * n * Real.log n ≤ j → j ≤ numPairs n →
        gnm n C j {g | ¬ ∀ x y : Fin n, ∃ l : List (Fin n), g.graph.IsWalkFrom x y l ∧
            WDigraph.hops l ≤ 2 * Nat.clog 2 n + 1 ∧
            l.IsChain (fun a b => g.2 (a, b) ≤ C * (512 * n * Real.log n / j))} ≤
          ENNReal.ofReal (c * (n : ℝ) ^ (-20 : ℝ)) ∧
        ∀ g : Sample n, (∀ x y : Fin n, ∃ l : List (Fin n), g.graph.IsWalkFrom x y l ∧
            WDigraph.hops l ≤ 2 * Nat.clog 2 n + 1 ∧
            l.IsChain (fun a b => g.2 (a, b) ≤ C * (512 * n * Real.log n / j))) →
          ∀ x y : Fin n, g.graph.dist x y ≤
            ENNReal.ofReal (C * (512 * n * Real.log n / j) * ((2 * Nat.clog 2 n + 1 : ℕ) : ℝ))
    := by sorry

end ExactDynamicSSSP.ExpectedUpdate
