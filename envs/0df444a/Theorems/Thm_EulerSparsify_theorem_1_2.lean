-- Prove2me | Theorems.Thm_EulerSparsify_theorem_1_2
-- name    : EulerSparsify.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:04.332087+00:00
-- url     : https://prove2.me/theorems/2d915e10-cbe7-4334-ad40-7eb42ecb1001
-- title:
--   Theorem 1.2 — every Eulerian graph has an $\varepsilon$-approximate Eulerian sparsifier with $O(\varepsilon^{-2}n)$ edges, computable in (randomized) polynomial time
-- statement:
--   This is the main theorem of the paper: linear-size Eulerian sparsifiers exist and can be computed in polynomial time.
--
--   There is a constant $C>0$ such that the following hold.
--
--   1. **Existence.** Let $\vec G=(V,E,w)$ be a finite Eulerian graph with nonnegative weights and $n=|V|$. For every $\varepsilon\in(0,1)$ there are new weights $w'$ such that $\vec H=(V,\mathrm{supp}(w'),w')$ is a reweighted subgraph of $\vec G$, $\vec H$ is Eulerian, and
--   $$\bigl\|L_G^{\dagger/2}(\vec L_{\vec G}-\vec L_{\vec H})L_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le\varepsilon,\qquad |E(\vec H)|=\mathrm{nnz}(w')\le C\,\varepsilon^{-2}\,n,$$
--   where $G=\mathrm{und}(\vec G)$.
--   2. **Polynomial time.** There is a polynomial $q$ and a Turing machine, running in time polynomial in its input length, that reads the binary encoding of a rational instance $(\vec G,\varepsilon,\delta)$ with $\vec G$ Eulerian, $\varepsilon\in(0,1)$, $\delta\in(0,1)$, together with $N=q(\text{encoding length})$ uniform random bits, and outputs new weights $w'$ (one per edge) satisfying item 1 with the same $C$, for at least a $1-\delta$ fraction of the $2^N$ coin strings.
--
--   The bound $O(\varepsilon^{-2}n)$ matches the optimal undirected bound of Batson, Spielman and Srivastava; previously the best existential bound for Eulerian graphs was off by a $\log n$ factor.
--
--   **Formalization Note** Definition 1.1 with the spectral norm and $L_G=B^\top WB$; machines are Mathlib's `TM2ComputableInPolyTime` with binary rationals.
--
--   Differences from the source:
--   - reading: "can be computed in polynomial time" → randomized TM2 polynomial-time algorithm with a polynomial-length coin string, success for at least a 1 − δ fraction of coin strings, δ ∈ (0,1) an input; reason: Theorem 1.2 is proved as Theorem 5.11 (succeeds with high probability; Gaussian sampling; poly(n, log U, log 1/δ)); a deterministic algorithm would be a different, unproved claim
--   - encoding: algorithm input (weighted graph, ε) → binary rational weights, ε and δ on a Mathlib TM2 machine, time polynomial in the encoding length; reason: a Turing machine reads finite inputs; real weights are covered by the existence clause
--   - generalization: "every Eulerian graph" → every finite Eulerian multigraph with nonnegative weights; parallel edges, self-loops, zero-weight edges and isolated vertices allowed; reason: merging parallel edges leaves L and the directed Laplacian unchanged and a sparsifier lifts; a loop has a zero row of B; simple graphs are a special case
--   - generalization: an ε-approximate Eulerian sparsifier H → H is a reweighted subgraph (V, supp(w'), w') of G; reason: a stronger conclusion, as in all the paper's constructions (p.1) and Algorithm 5.2
--   - encoding: |E(H)| = O(ε⁻²n), "such a sparsifier" → nnz(w') ≤ C ε⁻² n with one C for every graph, every ε ∈ (0,1) and both clauses; reason: the meaning of O(·) and of "such"
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Theorem 1.2, p.2 (PDF p.4); proved as Theorem 5.11, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_EulerSparsify_SparsifierWithin
import Definitions.Def_EulerSparsify_RatDigraph
import Definitions.Def_EulerSparsify_encSparsifyIn
import Definitions.Def_ReserveLB_encRatList
import Definitions.Def_KarpLiptonOM_countStr

namespace EulerSparsify

/-- **Theorem 1.2** (linear-size Eulerian sparsifiers, computable in polynomial time), p.2, PDF p.4
(proved as Theorem 5.11, p.23).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Theorem 1.2: "Every Eulerian graph ⃗G with n = |V| has, for every ε ∈ (0, 1), an
ε-approximate Eulerian sparsifier ⃗H with |E(⃗H)| = O(ε⁻²n), and such a sparsifier can be computed in
polynomial time."

There is one constant `C > 0` such that
* (existence) every finite Eulerian graph `⃗G = (V, E, w)` with nonnegative weights has, for every
  `ε ∈ (0, 1)`, a reweighted subgraph `⃗H = (V, supp(w'), w')` that is an ε-Eulerian spectral
  approximation of `⃗G` (Definition 1.1) with at most `C ε⁻² n` edges (`SparsifierWithin`); and
* (randomized polynomial time) one Turing machine, run on the binary encoding of `(⃗G, ε, δ)` with
  rational weights, `ε ∈ (0, 1)` and failure probability `δ ∈ (0, 1)`, and on a uniform coin string
  whose length `N` is a fixed polynomial of the encoding length, outputs the weights `w'` of such a
  sparsifier (same `C`) for at least a `1 − δ` fraction of the `2^N` coin strings.

**Formalization Note.**
* "Polynomial time" is randomized: the paper proves Theorem 1.2 by Theorem 5.11 ("succeeds with high
  probability"), whose algorithm draws a Gaussian (Proposition 3.10) and runs in
  `poly(n, log U, log 1/δ)`; the failure probability `δ` is an input and the time is polynomial in
  the binary length of `(⃗G, ε, δ)`. Machines are `Turing.TM2ComputableInPolyTime` with binary
  rationals (`encSparsifyInCoins`, `ReserveLB.encRatList`); the output list holds the new weights in edge
  order and must have one entry per edge.
* Multigraphs and self-loops are allowed; the graph may be disconnected and may have edges of
  weight `0` and isolated vertices. `|E(⃗H)|` is the number of nonzero new weights. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
          (G : DiGraph V E), (∀ e, 0 ≤ G.w e) → G.IsEulerian →
          ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ w' : E → ℝ, SparsifierWithin G ε C w') ∧
      ∃ (q : Polynomial ℕ) (alg : (RatDigraph × ℚ × ℚ) × List Bool → List ℚ),
        Nonempty (Turing.TM2ComputableInPolyTime encSparsifyInCoins ReserveLB.encRatList alg) ∧
        ∀ (I : RatDigraph) (hI : I.WellFormed) (ε δ : ℚ), (I.toDiGraph hI).IsEulerian →
          0 < ε → ε < 1 → 0 < δ → δ < 1 →
          (1 - (δ : ℝ)) * 2 ^ (q.eval (encSparsifyIn (I, ε, δ)).length) ≤
            (KarpLiptonOM.countStr (q.eval (encSparsifyIn (I, ε, δ)).length) fun cs =>
              (alg ((I, ε, δ), cs)).length = I.2.length ∧
                SparsifierWithin (I.toDiGraph hI) (ε : ℝ) C
                  (fun e => ((alg ((I, ε, δ), cs)).getD e.val 0 : ℝ)) : ℝ) := by sorry

end EulerSparsify
