-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_theorem_6_4
-- name    : ExactDynamicSSSP.ExpectedUpdate.theorem_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:01.222839+00:00
-- url     : https://prove2.me/theorems/b1ea4803-2153-4ebd-a230-613e48909c04
-- title:
--   Theorem 6.4 — logarithmic-squared expected work up to logarithmic average degree
-- statement:
--   For fixed $\varepsilon,K>0$ (and fixed $C>0$) there are constants $K'>0$, $n_0$ such that for all $n\ge\max(n_0,3)$, every source and every valid random update at an edge count $m$ with $(1+\varepsilon)n\le m\le Kn\log n$,
--   $$\mathbb ET\le K'\log^2n,$$
--   i.e. $\mathbb ET=O_{\varepsilon,K}(\log^2n)$.
--
--   Differences from the source:
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - reading: T = the update time of the implementation of Section 5 (unit-cost real additions/comparisons and pointer/record operations) → T = updateWork: the charged execution of Algorithm 1, Algorithm 3 and the indexed Fibonacci heap in the source pointer-operation model; reason: the source fixes the pointer implementation and unit-cost model but no charge table; the definition counts constant-size groups of its primitive operations, with scans, cuts, links and table visits charged explicitly
--   - reading: E T at edge count m → the t-th update of an arbitrary fixed valid operation-type sequence started from G_{n,m0}, with m the edge count of the graph receiving the update; reason: §6 fixes the type sequence in advance and Lemma 6.1 gives the law at every step; the proof of Lemma 6.3 (J_m = {m, m+1}) uses m as the count before the update
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: the updated arc is chosen uniformly among the existing (resp. missing) arcs → the arc of index ⌊U·k⌋ in a fixed enumeration of the k candidates, with U ~ U[0,1) independent of everything else; reason: this realizes exactly the uniform choice; the selection fails only on the null event U ∉ [0,1)
--   - reading: weight updates are decreases or increases → a weight change to an equal weight is processed by Algorithm 1 (record change only); reason: the source does not treat w' = w; in the random model it has probability 0
--   - encoding: H_x = hop count of the shortest path from s to x (unique almost surely) → H_x = depth of x in the certified shortest-path tree computed by the initialization (Dijkstra) on that graph, 0 if unreachable; reason: shortest paths are unique almost surely, so all expectations and probabilities are unchanged
--   - encoding: indexed edge and heap handles, adjacency lists, tree-child links, cached degrees and preferred incoming-record minima in the pointer-operation cost model → maps and lists specify pointer-structure contents extensionally; the cost counts their source operations, and processed/scanned sets are ghost observations; reason: map updates denote handle writes, erase denotes unlinking a known handle, adjacency and subtree enumerations charge their visited entries, and heap scans/links/promotions are charged explicitly; costs describe the source pointer program, not evaluation of the functional Lean representation
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Theorem 6.4, PDF p.12 = printed p.12

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Theorem 6.4 (PDF p. 12). For fixed `ε, K > 0` and `(1 + ε) n ≤ m ≤ K n log n`, the expected
actual work of a random update at edge count `m` is `O_{ε,K}(log² n)`. -/
theorem theorem_6_4 (C : ℝ) (hC : 0 < C) (ε K : ℝ) (hε : 0 < ε) (hK : 0 < K) :
    ∃ K' : ℝ, 0 < K' ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n →
      ∀ (s : Fin n) (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ), ValidOps n m₀ ops (t + 1) →
        (1 + ε) * n ≤ (edgeCount m₀ ops t : ℝ) →
        (edgeCount m₀ ops t : ℝ) ≤ K * n * Real.log n →
          expectedWork n C s m₀ ops t ≤ ENNReal.ofReal (K' * Real.log n ^ 2) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
