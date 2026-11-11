-- Prove2me | Theorems.Thm_BipMatchNC_Weighted_theorem_3_5
-- name    : BipMatchNC.Weighted.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:14:59.928214+00:00
-- url     : https://prove2.me/theorems/639e42be-0173-4fb8-bdac-fb7476118d82
-- title:
--   Theorem 3.5: for polynomially bounded weights, the maximum weight of a perfect matching (or the flag 'none') is computable in logspace-uniform NC²
-- statement:
--   For every constant $c$ there are a constant $c'$ and a logspace-uniform family $(C_N)$ of fan-in-2 Boolean circuits with $\mathrm{size}(C_N)\le N^{c'}+c'$ and
--   $$\mathrm{depth}(C_N)\le c'\lfloor\log_2N\rfloor^2+c'$$
--   which, on the code (of length $N$) of any balanced bipartite graph $G$ on $[n]+[n]$ with edge weights $w(e)\in\mathbb N$, $w(e)\le n^c+c$, outputs the bit $1$ followed by the binary code of $w^*$, the maximum weight of a perfect matching of $G$, if $G$ has a perfect matching, and the single bit $0$ otherwise.
--
--   This is the weighted decision step: by Lemma 3.9, $w^*$ is the integer closest to $\deg\mathcal D_w(t)/(2r)$, a quantity computable in $\mathrm{NC}^2$; Theorem 3.13 turns it into a search algorithm.
--
--   Differences from the source:
--   - reading: polynomially bounded edge weights → ∀ c : ℕ, instances with every edge weight ≤ n^c + c (WInstance.Bounded c); the circuit family may depend on c; reason: 'polynomially bounded' means bounded by some fixed polynomial in n; n^c + c dominates every polynomial for large enough c
--   - reading: the weight of the maximum weight perfect matching (if one exists) can be computed → output 1 followed by encNat w* when G.HasPM, and the single bit 0 otherwise; reason: the stronger reading: the circuit also reports when no perfect matching exists (Corollary 3.3 makes this available)
--   - encoding: in NC^k: logspace-uniform polynomial-size Boolean circuits of depth O(log^k n), n the input length → one constant c, a family C : ∀ N, BoolCircuit N (fan-in ≤ 2) with LogspaceUniform C, size ≤ N^c + c, depth ≤ c·⌊log₂ N⌋^k + c, all fixed before the input; reason: the §2 definition with the O(·) made an explicit constant; fan-in 2 is the usual convention for NC, and logspace uniformity uses the published transducer model
--   - encoding: a bipartite graph with edge weights w : E → ℕ, given as input → WInstance: n, G : BipGraph n, w : Fin n → Fin n → ℕ with w = 0 off the edges; code encNat n, n² adjacency bits row-major, then encNat of the n² weights row-major; reason: a standard injective binary encoding; only balanced graphs on [n] + [n] are inputs, since only balanced graphs have perfect matchings (p. 4), and an unbalanced input is answered 'none' by comparing the side sizes
--   - encoding: the output → a list y padded in the published (valid bit, data bit) format paddedOutput y ℓ with ℓ(N) ≤ N^c + c; reason: a circuit has a fixed number of outputs, while |y| varies
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 13 (PDF 14), Theorem 3.5

import Mathlib
import Definitions.Def_BipMatchNC_Weighted_NC
import Definitions.Def_BipMatchNC_Weighted_Problems

namespace BipMatchNC.Weighted

theorem theorem_3_5 (c : ℕ) :
    SearchInNC 2 (fun x : {x : WInstance // x.Bounded c} => x.1.enc)
      (fun x y => MaxPMWeightOutput x.1 y) := by sorry

end BipMatchNC.Weighted
