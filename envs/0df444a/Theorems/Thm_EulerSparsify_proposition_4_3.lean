-- Prove2me | Theorems.Thm_EulerSparsify_proposition_4_3
-- name    : EulerSparsify.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:40:27.702197+00:00
-- url     : https://prove2.me/theorems/064d50be-5ff5-471e-bdb6-428db6854530
-- title:
--   Proposition 4.3 — every weighted graph has a $c_{\mathrm{ner}}\, n/m$-nested ER partitioning, computable in polynomial time
-- statement:
--   There is a universal constant $c_{\mathrm{ner}}>0$ such that:
--
--   1. every finite weighted graph $G=(V,E,w)$ with positive weights, $n=|V|$ and $m=|E|$ has a $\bigl(c_{\mathrm{ner}}\cdot\tfrac nm\bigr)$-nested ER partitioning (Definition 2.1); and
--   2. one deterministic Turing machine computes such a partitioning, in time polynomial in the binary input length, from every input graph with positive rational weights.
--
--   The quality $O(n/m)$ does not depend on the edge weights; this removes the $\log n$ factor of earlier weak ER partitionings and is what makes linear-size sparsifiers possible.
--
--   **Formalization Note** Stated as `∃ c_ner > 0, NestedConst c_ner`; the machine writes the partitioning as a list of members $(U_i,E_i,F_i,j_i)$.
--
--   Differences from the source:
--   - reading: "computes in polynomial time" → existence for real weights and one deterministic TM2 machine on binary rational weights; reason: a Turing machine reads finite inputs; Algorithm 4.1 uses no randomness
--   - encoding: weighted graph → all weights positive; reason: Definition 2.1 uses w_min and b_i = 2^j w_min; applied to (V, supp(w), w_supp(w))
--   - reading: Definition 2.1 → IsNestedER: j ∈ ℤ, item 4 vertex-disjoint, diam_ER including connectivity; reason: the proof of Proposition 4.3 says the K_i of a bucket are vertex disjoint and K̂_i is connected as diam_ER ≤ ρ
--   - generalization: graph → parallel edges and self-loops allowed; reason: und of a digraph has parallel edges; Algorithm 4.1 never cuts a loop and Σ deg ≤ 2m still holds
--   - encoding: n/m at m = 0 → 0 (Lean division); reason: the empty family is a 0-nested partitioning then
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Proposition 4.3, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EulerSparsify_NestedConst

namespace EulerSparsify

/-- **Proposition 4.3** (existence and polynomial-time computation of a `c_ner · n/m`-nested ER
partitioning), p.13, PDF p.15.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Proposition 4.3: "There is an algorithm that given any weighted graph G = (V, E, w), with
n = |V|, m = |E|, computes in polynomial time a c_ner · n/m-nested ER partitioning for a universal
constant c_ner."

There is a universal constant `c_ner > 0` such that (`NestedConst c_ner`):
1. every finite weighted graph with positive weights, `n` vertices and `m` edges has a
   `(c_ner · n/m)`-nested ER partitioning (Definition 2.1); and
2. one Turing machine computes such a partitioning in time polynomial in the binary input length,
   from every input graph with positive rational weights.

**Formalization Note.** Positive weights: Definition 2.1 uses `w_min` and `b_i = 2^j w_min`, and
the proposition is applied to `(V, supp(w), w_supp(w))` (Algorithm 5.2, line 6). Parallel edges and
self-loops are allowed. The machine is deterministic (Algorithm 4.1 uses no randomness). -/
theorem proposition_4_3 : ∃ c_ner : ℝ, 0 < c_ner ∧ NestedConst c_ner := by sorry

end EulerSparsify
