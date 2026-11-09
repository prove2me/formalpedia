-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_theorem_6_1
-- name    : ExactDynamicSSSP.ExpectedUpdate.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:39:37.295695+00:00
-- url     : https://prove2.me/theorems/87af24a2-4f77-4259-801b-0dbc00a9d894
-- title:
--   Theorem 6.1 — expected update work across all edge counts, with exact queries and initialization
-- statement:
--   Consider the deterministic affected-region data structure (Algorithm 1 for insertions and weight decreases, Algorithm 3 for deletions and weight increases, a Fibonacci-heap global queue) under random single-arc updates in the uniform fixed-edge-count digraph $\mathcal G_{n,m}$, $n\ge3$, $N=n(n-1)$, with independent $U[0,C)$ weights and a source fixed independently of the graph. For every edge count $0\le m\le N$ of the graph receiving the update:
--
--   1. for each fixed $a\ge0$, $\mathbb ET=O_a(1)$ when $0\le m\le n+an^{2/3}$;
--   2. for each fixed $\gamma>1$ and $n\le m\le\gamma n$, $$\mathbb ET=O_\gamma\Bigl(\log^2n+\frac{(m-n)^3}{n^2}\log n\Bigr);$$
--   3. for each fixed $\varepsilon>0$, $\mathbb ET=O_\varepsilon(\log^2n)$ when $(1+\varepsilon)n\le m\le N$.
--
--   These bounds hold in expectation for each update; the work $T$ of each update is a random variable on the sample space. For arbitrary nonnegative real weights (zero weights and ties included), every reachable state stores exact distances and a shortest-path tree; a distance query returns the exact distance in $O(1)$ time, reporting a shortest path $\pi$ from $s$ to $v$ takes $O(|\pi|)$ time (and unreachability is reported in $O(1)$ time), and initialization takes $O(m+n\log n)$ time.
--
--   The three ranges overlap and together cover every edge count. The constants depend only on the indicated fixed parameters (and on $C$); the third bound is not asserted uniformly as $\varepsilon\downarrow0$.
--
--   Differences from the source:
--   - encoding: O-bounds whose constants may depend on the displayed fixed parameters (C > 0 fixed) → ∀ C > 0, ∀ fixed parameters, ∃ K > 0, ∃ n₀, ∀ n ≥ n₀ with n ≥ 3, ∀ source, initial count, operation sequence and step; reason: standard meaning of O with the constant chosen before n, m and the update
--   - reading: T = the update time of the implementation of Section 5 (unit-cost real additions/comparisons and pointer/record operations) → T = updateWork: the charged execution of Algorithm 1, Algorithm 3 and the indexed Fibonacci heap in the source pointer-operation model; reason: the source fixes the pointer implementation and unit-cost model but no charge table; the definition counts constant-size groups of its primitive operations, with scans, cuts, links and table visits charged explicitly
--   - reading: E T at edge count m → the t-th update of an arbitrary fixed valid operation-type sequence started from G_{n,m0}, with m the edge count of the graph receiving the update; reason: §6 fixes the type sequence in advance and Lemma 6.1 gives the law at every step; the proof of Lemma 6.3 (J_m = {m, m+1}) uses m as the count before the update
--   - encoding: conditional on the arc set, the present arcs carry independent U[0,C) weights → a U[0,C) weight is drawn independently for each of the n² ordered pairs (including unused diagonal coordinates), and the graph uses the weights of its present arcs (truncated at 0, a null event); reason: the weighted graph has exactly the source's law
--   - encoding: the updated arc is chosen uniformly among the existing (resp. missing) arcs → the arc of index ⌊U·k⌋ in a fixed enumeration of the k candidates, with U ~ U[0,1) independent of everything else; reason: this realizes exactly the uniform choice; the selection fails only on the null event U ∉ [0,1)
--   - reading: weight updates are decreases or increases → a weight change to an equal weight is processed by Algorithm 1 (record change only); reason: the source does not treat w' = w; in the random model it has probability 0
--   - encoding: H_x = hop count of the shortest path from s to x (unique almost surely) → H_x = depth of x in the certified shortest-path tree computed by the initialization (Dijkstra) on that graph, 0 if unreachable; reason: shortest paths are unique almost surely, so all expectations and probabilities are unchanged
--   - generalization: 'These bounds hold in expectation for each update' → additionally asserts that the work of every update is a measurable function on the sample space; reason: makes the lower integral the expectation of the random variable T; it is implied by the source's use of E T
--   - generalization: 'Distance queries take O(1) time and reporting a path π takes O(|π|) time' → additionally asserts that every reachable state stores exact distances and a shortest-path tree, that a query returns the exact distance, and that path reporting returns a shortest simple path from s to v, as a repetition-free vertex list (or reports unreachability exactly when the distance is ∞); reason: the abstract, §3.5 and Appendix A state that the queries are exact and the tree is a shortest-path tree; the time bounds are about these exact queries
--   - encoding: |π| the length of the reported path → the number of emitted vertices (the trivial path to s has one vertex); reason: O(|π|) is unchanged by the ±1
--   - encoding: indexed edge and heap handles, adjacency lists, tree-child links, cached degrees and preferred incoming-record minima in the pointer-operation cost model → maps and lists specify pointer-structure contents extensionally; the cost counts their source operations, and processed/scanned sets are ghost observations; reason: map updates denote handle writes, erase denotes unlinking a known handle, adjacency and subtree enumerations charge their visited entries, and heap scans/links/promotions are charged explicitly; costs describe the source pointer program, not evaluation of the functional Lean representation
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Theorem 6.1, PDF pp.7–8 = printed pp.7–8 (statement continues on p.8); proof of Theorem 6.1, PDF p.12

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_RandomModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- **Theorem 6.1** (PDF pp. 7–8). For the deterministic affected-region data structure
(Algorithm 1, Algorithm 3, Fibonacci-heap global queue) and random single-arc updates in the
uniform fixed-edge-count digraph with independent `U[0, C)` weights, for every edge count
`0 ≤ m ≤ N` before the update:
1. for each fixed `a ≥ 0`, `𝔼T = O_a(1)` when `0 ≤ m ≤ n + a n^{2/3}`;
2. for each fixed `γ > 1` and `n ≤ m ≤ γ n`, `𝔼T = O_γ(log² n + ((m - n)³/n²) log n)`;
3. for each fixed `ε > 0`, `𝔼T = O_ε(log² n)` when `(1 + ε) n ≤ m ≤ N`.
These bounds hold in expectation for each update (the work `T` is a random variable). The data
structure maintains exact distances and a shortest-path tree for arbitrary nonnegative real
weights; distance queries take `O(1)` time, reporting a shortest path `π` takes `O(|π|)` time,
and initialization takes `O(m + n log n)` time. -/
theorem theorem_6_1 :
    (∀ C : ℝ, 0 < C → ∀ a : ℝ, 0 ≤ a → ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n →
      ∀ (s : Fin n) (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ), ValidOps n m₀ ops (t + 1) →
        (edgeCount m₀ ops t : ℝ) ≤ n + a * (n : ℝ) ^ ((2 : ℝ) / 3) →
          expectedWork n C s m₀ ops t ≤ ENNReal.ofReal K) ∧
    (∀ C : ℝ, 0 < C → ∀ γ : ℝ, 1 < γ → ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n →
      ∀ (s : Fin n) (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ), ValidOps n m₀ ops (t + 1) →
        n ≤ edgeCount m₀ ops t → (edgeCount m₀ ops t : ℝ) ≤ γ * n →
          expectedWork n C s m₀ ops t ≤
            ENNReal.ofReal (K * (Real.log n ^ 2 +
              ((edgeCount m₀ ops t : ℝ) - n) ^ 3 / (n : ℝ) ^ 2 * Real.log n))) ∧
    (∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 3 ≤ n →
      ∀ (s : Fin n) (m₀ : ℕ) (ops : ℕ → UpdKind) (t : ℕ), ValidOps n m₀ ops (t + 1) →
        (1 + ε) * n ≤ (edgeCount m₀ ops t : ℝ) →
          expectedWork n C s m₀ ops t ≤ ENNReal.ofReal (K * Real.log n ^ 2)) ∧
    (∀ (n : ℕ) (s : Fin n) (ops : ℕ → UpdKind) (t : ℕ),
      Measurable (fun ω : Omega n (t + 1) => updateWork s ops (t + 1) ω t)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (G : WDigraph n) (s : Fin n) (ds : DS n),
      IsReachableState G s ds →
        IsSPT G s ds.par ∧ ∀ v : Fin n,
          (distQuery ds v).1 = G.dist s v ∧ ((distQuery ds v).2 : ℝ) ≤ K ∧
          (∀ l, (pathReport ds v).1 = some l →
            G.IsWalkFrom s v l ∧ l.Nodup ∧ G.walkWeight l = G.dist s v ∧
              ((pathReport ds v).2 : ℝ) ≤ K * l.length) ∧
          ((pathReport ds v).1 = none → G.dist s v = ⊤ ∧ ((pathReport ds v).2 : ℝ) ≤ K)) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (G : WDigraph n) (s : Fin n),
      ((initDS G s).cost : ℝ) ≤ K * (G.numArcs + n * Real.log n)) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
