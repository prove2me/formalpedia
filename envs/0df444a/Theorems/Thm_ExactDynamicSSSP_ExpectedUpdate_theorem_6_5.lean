-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_theorem_6_5
-- name    : ExactDynamicSSSP.ExpectedUpdate.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:17.118082+00:00
-- url     : https://prove2.me/theorems/47bd8446-21ec-401f-9b99-7e23fbcf66b0
-- title:
--   Theorem 6.5 — dense regime: subtree sizes and logarithmic-squared update work
-- statement:
--   Fix $C>0$. There are constants $K>0$, $n_0$ such that for $n\ge\max(n_0,3)$ and every source:
--
--   1. for every $512\,n\log n\le j\le N$, a uniformly chosen existing arc $e$ satisfies
--   $$\mathbb E_j\,q(e)\le K\,\frac{n\log^2n}{j},\qquad \mathbb E_j\bigl(f^+(e)+f^-(e)\bigr)\le K\log^2n;$$
--   2. in this range the expected work of a valid random update at edge count $m\ge512\,n\log n$ is $\mathbb ET\le K\log^2n$.
--
--   That is, $\mathbb E_jq(e)=O(n\log^2n/j)$, $\mathbb E_j(f^+(e)+f^-(e))=O(\log^2n)$ and $\mathbb ET=O(\log^2n)$.
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
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Theorem 6.5, PDF p.12 = printed p.12

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Theorem 6.5 (PDF p. 12). For `j ≥ 512 n log n`, a uniformly chosen existing arc `e`
satisfies `𝔼_j q(e) = O(n log² n / j)` and `𝔼_j (f⁺(e) + f⁻(e)) = O(log² n)`; in this range the
expected actual work of a random update is `O(log² n)`. -/
theorem theorem_6_5 (C : ℝ) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n → ∀ s : Fin n,
      (∀ j : ℕ, 512 * n * Real.log n ≤ j → j ≤ numPairs n →
        ∫⁻ g, arcAverage g.graph (subtreeSize s (spt g.graph s)) ∂(gnm n C j) ≤
            ENNReal.ofReal (K * n * Real.log n ^ 2 / j) ∧
        ∫⁻ g, arcAverage g.graph
            (fun e => subtreeOut g.graph s (spt g.graph s) e + subtreeIn g.graph s (spt g.graph s) e)
            ∂(gnm n C j) ≤ ENNReal.ofReal (K * Real.log n ^ 2)) ∧
      (∀ (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ), ValidOps n m₀ ops (t + 1) →
        512 * n * Real.log n ≤ (edgeCount m₀ ops t : ℝ) →
          expectedWork n C s m₀ ops t ≤ ENNReal.ofReal (K * Real.log n ^ 2)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
