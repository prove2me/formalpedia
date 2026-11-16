-- Prove2me | Theorems.Thm_DecodablePOMDP_Supplement_theorem_7
-- name    : DecodablePOMDP.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:46:51.342051+00:00
-- url     : https://prove2.me/theorems/03a7f24a-d2ba-4ad9-84ad-438a2848209a
-- title:
--   Theorem 7 — a kernel $K_G$ built in polynomial time with $\gamma(K_G)=\frac{n}{2m}\phi(G)$
-- statement:
--   There is a polynomial-time algorithm that, given a simple graph $G=(V,E)$ with $n\ge2$ vertices and $m\ge1$ edges, outputs a rational observation kernel $K_G$ from $V$ to a finite observation set (every $K_G(\cdot\mid s)$ a probability vector) such that
--
--   $$\gamma(K_G)=\frac{n}{2m}\,\phi(G),$$
--
--   where $\gamma(K)=\inf_{v\in\mathbf 1^\perp,\,v\ne0}\|Kv\|_1/\|v\|_1$ is the optimal $\ell_1$-observability parameter and $\phi(G)=\min_{\emptyset\ne A\subsetneq V}|\partial A|/(|A|(n-|A|))$ the uniform sparsest-cut value.
--
--   Precisely: there are a degree $k$ and one Turing machine that, on the binary code of every such graph (vertex count and adjacency matrix), halts within $(\text{input length}+2)^k$ steps with the binary code of such a kernel.
--
--   Since computing $\phi(G)$ is NP-hard, this shows that the optimal $\ell_1$-observability constant can be hard to compute, unlike the decodability constant, which is the value of a linear program.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) with n vertices and m edges → a `GraphInput`: `n` and a symmetric zero-diagonal adjacency matrix (`IsValid`), coded as `encodeNat n` followed by its n² bits; the simple graph `toGraph` on `Fin n`; m = `numEdges`, the adjacent pairs i < j; reason: E is a set of edges, so G is a simple graph; the adjacency matrix is the standard input encoding of a graph and makes the input size at least n, which any construction with one column per vertex needs
--   - encoding: one can construct … in polynomial time → ∃ k, ∃ one Mathlib TM2 machine M (`HMBinPacking.OutputsWithin`) that on the binary code of every valid input with n ≥ 2, m ≥ 1 halts within (input length + 2)^k steps; reason: the base mission's machine model for "polynomial time"; poly(input size) = (input length + 2)^k
--   - encoding: an observation kernel K_G ∈ ℝ^{O×S} → the machine outputs the code of a rational matrix K : Fin n → Fin O → ℚ (`K s y = K_G(y | s)`, states = vertices, O part of the output), each `K(· | s)` a probability vector; reason: a machine output is a finite object; the stochasticity is the clause "observation kernel"
--   - reading: In other words, computing the optimal ℓ1-observability constant for K_G is NP-hard. → not stated; reason: it restates the theorem through the cited NP-hardness of uniform sparsest cut [Bonsma et al. 2012] without fixing a computational problem or encoding; the theorem's content is the polynomial-time construction and the identity, both stated
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Theorem 7, p.28 (proof pp.28–30); Definition 5, p.28

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_DecodablePOMDP_Supplement_Observability
import Definitions.Def_DecodablePOMDP_Supplement_SparsestCut

namespace DecodablePOMDP.Supplement

open CalibratedCE.Forecast

/-- **Theorem 7 (the optimal ℓ1-observability constant encodes the uniform sparsest cut).** There
are a degree `k` and one Turing machine `M` such that, for every simple graph `G` on `Fin n`, given
by its adjacency matrix, with `n ≥ 2` vertices and `m ≥ 1` edges, `M` started on the binary code
of `G` halts within `(input length + 2)^k` steps with the binary code of a rational matrix
`K_G : V × [O] → ℚ` such that
1. `K_G` is an observation kernel: every `K_G(· | s)`, `s ∈ V`, is a probability vector on `[O]`;
2. `γ(K_G) = (n / (2m)) · ϕ(G)`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Theorem 7, p.28 (proof pp.28–30): "Given a graph G with n ≥ 2 vertices and m ≥ 1
edges, one can construct an observation kernel K_G in polynomial time such that
γ(K_G) = (n/(2m)) ϕ(G). In other words, computing the optimal ℓ1-observability constant for K_G is
NP-hard."

**Formalization Note.**
* "a graph": a simple graph on `V = Fin n` (E is a set of edges), input as `n` (binary `encodeNat`)
  and its symmetric, zero-diagonal adjacency matrix (`GraphInput.IsValid`), the standard encoding;
  `m = numEdges` is the number of pairs `i < j` that are adjacent.
* "in polynomial time": steps of one Mathlib multi-stack Turing machine (`HMBinPacking.OutputsWithin`,
  the base mission's machine model), at most `(n_in + 2)^k` with `n_in` the input length.
* States of `K_G` are the vertices; its number `O` of observations is part of the output.
* The closing sentence ("In other words, … NP-hard") restates the theorem through a cited result
  [Bonsma et al. 2012] without fixing a computational problem, and is not stated. -/
theorem theorem_7 :
    ∃ k : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
    ∀ I : GraphInput, I.IsValid → 2 ≤ I.n → 1 ≤ I.numEdges →
      ∃ (O : ℕ) (K : Fin I.n → Fin O → ℚ) (t : ℕ),
        HMBinPacking.OutputsWithin M (encodeGraph I) (encodeKernel K) t ∧
        t ≤ ((encodeGraph I).length + 2) ^ k ∧
        (∀ s, IsDist (fun y => (K s y : ℝ))) ∧
        optL1Obs (fun s y => (K s y : ℝ)) =
          (I.n : ℝ) / (2 * (I.numEdges : ℝ)) * sparsestCut I.toGraph := by sorry

end DecodablePOMDP.Supplement
