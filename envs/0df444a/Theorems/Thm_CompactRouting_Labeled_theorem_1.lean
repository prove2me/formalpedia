-- Prove2me | Theorems.Thm_CompactRouting_Labeled_theorem_1
-- name    : CompactRouting.Labeled.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:27.021466+00:00
-- url     : https://prove2.me/theorems/da0a2b66-a70e-4c4e-a11b-a12877b8d9fa
-- title:
--   Theorem 1 — a labeled routing scheme with expected stretch $2k-1$, $\tilde O(n^{1/k})$ average storage, $\tilde O(k)$ labels and $\tilde O(1)$ headers
-- statement:
--   For every weight exponent $a\in\mathbb N$ there are constants $C,c$ such that for every integer $k\ge2$ there is one labeled routing scheme $S$ (deterministic preprocessing, randomized source rule, deterministic forwarding rule; the two rules independent of the instance) with the following property. For every connected simple graph $G$ on $n$ vertices with integer edge weights in $[1,n^a]$ and every port numbering, writing $\lambda=(\lfloor\log_2 n\rfloor+1)$:
--   $$\sum_{u\in V}|RT(u)|\le C\,n^{1+1/k}\lambda^c,\qquad |L(v)|\le C\,k\,\lambda^c\ \ (v\in V),$$
--   and for all $u,v\in V$: every outcome of the source's coins that has positive probability delivers the message to $v$ with every header of at most $C\lambda^c$ bits, and
--   $$\mathbb E\big[\hat d(u,v)\big]\le(2k-1)\,d(u,v),$$
--   the expectation over the source's coins only. Sizes are in bits; the average local storage is the total divided by $n$, i.e. $\tilde O(n^{1/k})$ words. Under the Erdős girth conjecture the stretch $2k-1$ is optimal for this storage (Lemma 6 of the paper).
--
--   Differences from the source:
--   - generalization: every integer k ≥ 2 with the Õ bounds under the paper's tacit k ≤ log n (proof of Lemma 7) → every k ≥ 2 with C, c independent of k; reason: a scheme may use min(k, max(2, ⌊log₂ n⌋)) levels, which lowers the stretch and keeps n^{1/k′} within a constant of n^{1/k}; the statement specializes to k ≤ log n
--   - encoding: storage, labels and headers in words of O(log n) bits; Õ hides polylogarithmic factors in n; average storage = total / n → bits; C·g·(⌊log₂ n⌋+1)^c with C, c depending only on the weight exponent a; the total table size bounded by C·n^{1+1/k}·(…)^c; reason: a word is Θ(log n) bits, absorbed in the polylog
--   - reading: weights 'polynomially bounded integers, possibly after rescaling' (fn. 5) → integer weights in [1, n^a] for a fixed a ∈ ℕ, constants depending on a; reason: fn. 5; a real exponent is bounded by a natural one
--   - reading: a labeled routing scheme (§1 p. 2, §2 p. 5, fn. 6): preprocessing fixes tables and labels, only the source flips coins, the forwarding uses the vertex's table, the destination's label and the header, fixed ports → `Scheme`: deterministic table/label maps of the whole instance (graph and ports), a source rule from (RT(u), L(v)) to a finitely supported distribution with rational masses on (first port, header), a deterministic forwarding rule from (RT(x), L(v), header) to (port, header); one scheme for all instances, every port numbering; reason: the routing model as the paper describes it; fn. 6 gives the rational masses; no running time is part of Theorem 1
--   - encoding: d̂(u, v), 'the length of the walk that a message traverses from u to v', and 'headers of Õ(1) words' → the weighted length of the walk up to its first arrival at v (edges with repetition); every header carried on a hop before that arrival is bounded; every positive-probability outcome must deliver; reason: the message stops when it reaches the destination; u = v gives the empty walk
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 3, Theorem 1 (restated and proved p. 14)

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 3, Theorem 1 (restated and proved p. 14):
"For every integer k ≥ 2, there is a (2k − 1)-expected stretch labeled compact routing scheme that
uses average local storage of Õ(n^{1/k}) words, labels of Õ(k) words, and headers of Õ(1) words."
For every weight exponent `a` there are constants `C, c` such that for every `k ≥ 2` there is one
scheme `S` (preprocessing, source rule, forwarding rule) such that on every connected simple graph
with integer weights in `[1, n^a]` and every port numbering: the tables have at most
`C·n^{1+1/k}·(⌊log₂ n⌋+1)^c` bits in total, every label at most `C·k·(⌊log₂ n⌋+1)^c` bits, and for
every source `u` and destination `v`, every outcome of the source's coins with positive probability
delivers the message with headers of at most `C·(⌊log₂ n⌋+1)^c` bits, and
`E[d̂(u, v)] ≤ (2k − 1)·d(u, v)`. -/
theorem theorem_1 :
    ∀ a : ℕ, ∃ C c : ℕ, ∀ k : ℕ, 2 ≤ k → ∃ S : Scheme, ∀ I : Instance, I.Valid a →
      (∑ u : Fin I.G.n, ((S.table I u).length : ℝ)) ≤
          C * (I.G.n : ℝ) ^ (1 + 1 / (k : ℝ)) * ((Nat.log 2 I.G.n : ℝ) + 1) ^ c ∧
        (∀ v : Fin I.G.n,
          ((S.label I v).length : ℝ) ≤ C * k * ((Nat.log 2 I.G.n : ℝ) + 1) ^ c) ∧
        ∀ u v : Fin I.G.n,
          (∀ o ∈ S.srcSupport I u v, S.Delivered I u v o ∧
              S.HeadersBounded I u v o (C * ((Nat.log 2 I.G.n : ℝ) + 1) ^ c)) ∧
            S.expectedLength I u v ≤ (2 * (k : ℝ) - 1) * dist I.G u v := by sorry

end CompactRouting.Labeled
