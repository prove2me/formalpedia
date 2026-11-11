-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_theorem_1_1
-- name    : BipMatchNC.Weighted.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:58.822982+00:00
-- url     : https://prove2.me/theorems/e291b34d-64b2-4375-a4f8-82403641a123
-- title:
--   Theorem 1.1: a maximum weight perfect matching of a bipartite graph with polynomially bounded edge weights can be found in NC
-- statement:
--   For every constant $c$ there are an exponent $k$, a constant $c'$ and a logspace-uniform family $(C_N)_{N\in\mathbb N}$ of fan-in-2 Boolean circuits with
--   $$\mathrm{size}(C_N)\le N^{c'}+c',\qquad \mathrm{depth}(C_N)\le c'\lfloor\log_2N\rfloor^{k}+c',$$
--   $N$ the input length, which on the code of any balanced bipartite graph $G$ on $[n]+[n]$ with edge weights $w:E\to\mathbb N$, $w(e)\le n^c+c$, output the bit $1$ followed by the edge set of a perfect matching of $G$ of maximum total weight whenever $G$ has a perfect matching, and the bit $0$ ("no perfect matching") when it has none.
--
--   This is the paper's headline result: bipartite perfect matching, decision and search, weighted with polynomially bounded weights, is in deterministic $\mathrm{NC}$, settling a question open since the randomized $\mathrm{NC}$ algorithms of the 1980s; the previous deterministic bound was quasi-$\mathrm{NC}$.
--
--   Differences from the source:
--   - reading: polynomially bounded edge weights → ∀ c : ℕ, instances with every edge weight ≤ n^c + c (WInstance.Bounded c); the circuit family may depend on c; reason: 'polynomially bounded' means bounded by some fixed polynomial in n; n^c + c dominates every polynomial for large enough c
--   - reading: finding a maximum weight perfect matching → output 1 followed by the n² row-major bits of the edge set of a maximum weight perfect matching when G.HasPM, and 0 followed by n² zeros otherwise; reason: the stronger reading of 'finding': the circuit must also report that there is no perfect matching (Corollary 3.3 makes this free)
--   - encoding: is in NC: in NC^k for some k, by logspace-uniform polynomial-size Boolean circuits of depth O(log^k n), n the input length → ∃ k, one constant c', a family C : ∀ N, BoolCircuit N (fan-in ≤ 2) with LogspaceUniform C, size ≤ N^c' + c', depth ≤ c'·⌊log₂ N⌋^k + c', all fixed before the input (SearchInNC k); reason: §2: NC = ∪_k NC^k, with the O(·) made an explicit constant fixed before the input; fan-in 2 is the usual convention for NC
--   - encoding: a bipartite graph with edge weights w : E → ℕ, given as input → WInstance: n, G : BipGraph n, w : Fin n → Fin n → ℕ with w = 0 off the edges; code encNat n, n² adjacency bits row-major, then encNat of the n² weights row-major; reason: a standard injective binary encoding; only balanced graphs on [n] + [n] are inputs, since only balanced graphs have perfect matchings (p. 4), and an unbalanced input is answered 'none' by comparing the side sizes
--   - encoding: the output → a list y padded in the published (valid bit, data bit) format paddedOutput y ℓ with ℓ(N) ≤ N^c + c; reason: standard format for a circuit with a fixed number of outputs
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 2 (PDF 3), Theorem 1.1

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_NC
import Definitions.Def_BipMatchNC_Weighted_Problems

namespace BipMatchNC.Weighted

theorem theorem_1_1 : ∀ c : ℕ, ∃ k : ℕ,
    SearchInNC k (fun x : {x : WInstance // x.Bounded c} => x.1.enc)
      (fun x y => MaxWeightPMOutput x.1 y) := by sorry

end BipMatchNC.Weighted
