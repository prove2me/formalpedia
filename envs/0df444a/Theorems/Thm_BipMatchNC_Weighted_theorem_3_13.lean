-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_theorem_3_13
-- name    : BipMatchNC.Weighted.theorem_3_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:57.189195+00:00
-- url     : https://prove2.me/theorems/65ddc0d9-2b40-4dde-a04f-61740564a2f5
-- title:
--   Theorem 3.13: a maximum weight perfect matching of a bipartite graph with polynomially bounded weights is computable in logspace-uniform NC³
-- statement:
--   For every constant $c$ there are a constant $c'$ and a logspace-uniform family $(C_N)$ of fan-in-2 Boolean circuits with $\mathrm{size}(C_N)\le N^{c'}+c'$ and
--   $$\mathrm{depth}(C_N)\le c'\lfloor\log_2N\rfloor^3+c'$$
--   which, on the code (of length $N$) of any balanced bipartite graph $G$ on $[n]+[n]$ with edge weights $w(e)\in\mathbb N$, $w(e)\le n^c+c$, outputs the bit $1$ followed by the edge set of a perfect matching of maximum total weight if $G$ has a perfect matching, and the bit $0$ (no perfect matching) otherwise.
--
--   The search algorithm runs the Fenner–Gurjar–Thierauf isolation scheme as an $\mathrm{NC}$ reduction to the weight computation of Theorem 3.5, over $\log n$ rounds; the depth exponent $3$ is uniform in $c$, which is stronger than the $\exists k$ of Theorem 1.1.
--
--   Differences from the source:
--   - reading: a maximum weight perfect matching in a weighted bipartite graph (no bound on the weights) → polynomially bounded weights: ∀ c, instances with every edge weight ≤ n^c + c (WInstance.Bounded c), depth exponent 3 for every c; reason: obvious omission (finding I2): the proof is 'Using Theorem 3.5', which assumes polynomially bounded weights, and Theorems 1.1 and 4.18 carry the qualifier
--   - reading: finding a maximum weight perfect matching → output 1 followed by the n² row-major bits of the edge set of a maximum weight perfect matching when G.HasPM, and 0 followed by n² zeros otherwise; reason: the stronger reading of 'finding': the circuit must also report that there is no perfect matching (Corollary 3.3 makes this free)
--   - encoding: in NC³: logspace-uniform polynomial-size Boolean circuits of depth O(log³ n), n the input length → one constant c', a family C : ∀ N, BoolCircuit N (fan-in ≤ 2) with LogspaceUniform C, size ≤ N^c' + c', depth ≤ c'·⌊log₂ N⌋³ + c', all fixed before the input; reason: the §2 definition with the O(·) made an explicit constant; fan-in 2 is the usual convention for NC
--   - encoding: a bipartite graph with edge weights w : E → ℕ, given as input → WInstance: n, G : BipGraph n, w : Fin n → Fin n → ℕ with w = 0 off the edges; code encNat n, n² adjacency bits row-major, then encNat of the n² weights row-major; reason: a standard injective binary encoding; only balanced graphs on [n] + [n] are inputs, since only balanced graphs have perfect matchings (p. 4), and an unbalanced input is answered 'none' by comparing the side sizes
--   - encoding: the output → a list y padded in the published (valid bit, data bit) format paddedOutput y ℓ with ℓ(N) ≤ N^c + c; reason: standard format for a circuit with a fixed number of outputs
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 19 (PDF 20), Theorem 3.13

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_NC
import Definitions.Def_BipMatchNC_Weighted_Problems

namespace BipMatchNC.Weighted

theorem theorem_3_13 (c : ℕ) :
    SearchInNC 3 (fun x : {x : WInstance // x.Bounded c} => x.1.enc)
      (fun x y => MaxWeightPMOutput x.1 y) := by sorry

end BipMatchNC.Weighted
