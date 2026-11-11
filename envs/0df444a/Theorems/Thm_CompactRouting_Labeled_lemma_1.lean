-- Prove2me | Theorems.Thm_CompactRouting_Labeled_lemma_1
-- name    : CompactRouting.Labeled.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:06:47.862341+00:00
-- url     : https://prove2.me/theorems/27832bc6-6820-4ee2-8a13-000ec314732c
-- title:
--   Lemma 1 — a deterministic hierarchy with $|A_i|=\tilde O(n^{1-i/k})$ and $|B_i(u)|=\tilde O(n^{1/k})$
-- statement:
--   There are constants $C,c$ such that for every connected simple graph $G$ with $n$ vertices and positive edge weights and every integer $k\ge2$ there is a hierarchy $V=A_0\supseteq A_1\supseteq\cdots\supseteq A_{k-1}\supseteq A_k=\emptyset$ with $A_{k-1}\neq\emptyset$ such that for every $i\in[k]$ and $u\in V$
--   $$|A_i|\le C\,n^{1-i/k}(\lfloor\log_2 n\rfloor+1)^c,\qquad |B_i(u)|\le C\,n^{1/k}(\lfloor\log_2 n\rfloor+1)^c,$$
--   where $B_i(u)=\{w\in A_i : d(u,w)<d(u,A_{i+1})\}$. This is the hierarchy (Roditty–Thorup–Zwick, via Kadria–Roditty) behind every storage bound of the average-storage schemes.
--
--   Differences from the source:
--   - encoding: 'we can deterministically compute' the sets → existence of the hierarchy; reason: no running time is claimed; existence is what the scheme uses (its preprocessing is an arbitrary deterministic map)
--   - encoding: Õ(·) hiding polylogarithmic factors in n → C·g·(⌊log₂ n⌋+1)^c with C, c independent of the graph and of k; reason: the paper's Õ convention (fn. 3); the constants of an Õ bound do not depend on the instance
--   - generalization: sets V = A_0 ⊇ ⋯ ⊇ A_{k−1} ⊇ A_k = ∅ → a published `Hierarchy`, which also has A_{k−1} ≠ ∅; reason: a stronger conclusion: adding one vertex to every A_i with 1 ≤ i < k keeps the bounds; the paper's pivots need A_{k−1} ≠ ∅
--   - encoding: G = (V, E, ℓ) connected undirected with positive weights, vertices with identifiers 1..n → published edge-list `TZLevelsADO.Graph` on `Fin n` with hypotheses `IsSimple`, `PosWeights`, `Connected`; reason: Lean convention; same instances
-- source:
--   Lifshitz, Chechik, Kadria, Roditty, Optimal (Randomized) Compact Routing Schemes, arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 1

import Mathlib
import Definitions.Def_CompactRouting_Labeled_Scheme
import Definitions.Def_CompactRouting_Labeled_Clusters

open TZLevelsADO

namespace CompactRouting.Labeled

/-- Lifshitz, Chechik, Kadria, Roditty, *Optimal (Randomized) Compact Routing Schemes*,
arXiv:2611.04744 (held version, sha256 d7e0fc67…), p. 6, Lemma 1 (Lemma 1 of [KR25a]):
"For every integer k ≥ 2, we can deterministically compute sets V = A_0 ⊇ ⋯ ⊇ A_{k−1} ⊇ A_k = ∅
with |A_i| = Õ(n^{1−i/k}) and |B_i(u)| = Õ(n^{1/k}), for every i ∈ [k] and u ∈ V."
`Õ(g)` is `C·g·(⌊log₂ n⌋ + 1)^c` with constants `C, c` independent of the graph and of `k`;
the hierarchy produced also has `A_{k−1} ≠ ∅` (part of `Hierarchy`). -/
theorem lemma_1 :
    ∃ C c : ℕ, ∀ (G : Graph) (k : ℕ), IsSimple G → G.PosWeights → G.Connected → 2 ≤ k →
      ∃ A : Hierarchy G k, ∀ i < k,
        ((A.A i).card : ℝ) ≤ C * (G.n : ℝ) ^ (1 - (i : ℝ) / k) * ((Nat.log 2 G.n : ℝ) + 1) ^ c ∧
        ∀ u : Fin G.n,
          ((bunchAt A i u).card : ℝ) ≤ C * (G.n : ℝ) ^ (1 / (k : ℝ)) * ((Nat.log 2 G.n : ℝ) + 1) ^ c := by sorry

end CompactRouting.Labeled
