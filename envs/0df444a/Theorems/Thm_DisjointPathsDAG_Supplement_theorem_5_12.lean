-- Prove2me | Theorems.Thm_DisjointPathsDAG_Supplement_theorem_5_12
-- name    : DisjointPathsDAG.Supplement.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:01:22.019579+00:00
-- url     : https://prove2.me/theorems/08672a63-91d3-43b1-80e2-1774ee483fbe
-- title:
--   Theorem 5.12 — two disjoint shortest paths in expected linear time on DAGs and on undirected graphs
-- statement:
--   Let $G$ have $n$ vertices, $m$ edges, and two terminal pairs $(s_1,t_1)$, $(s_2,t_2)$ whose four terminals are pairwise distinct. Consider two cases:
--
--   - **(DAG)** $G$ is a directed acyclic graph (parallel edges allowed) with arbitrary real edge weights, handled by exact unit-cost additions, subtractions and comparisons;
--   - **(undirected)** $G$ is an undirected graph with integer edge weights $1\le w(e)\le (m+n)^b$ for a constant $b$, stored in machine words.
--
--   The machine is the word RAM of Section 2.1 with $\Theta(\log(m+n))$-bit words and a field $\mathbb F_{2^q}$, $q=O(\log(m+n))$, with unit-cost field operations and uniform sampling. For every $b$ there is a constant $C$ such that for every $c>0$ there are randomized algorithms with the following guarantees in both cases:
--
--   1. **Monte Carlo reporting.** The expected running time is at most $C\,(m+n)$, at most $C\,(m+n)$ storage cells are used on every run, the algorithm never returns an invalid pair, returns "no" on every infeasible instance, and reports two vertex-disjoint shortest $s_i$–$t_i$ paths with probability at least
--   $$1-(m+n)^{-c}$$
--   on every feasible instance.
--   2. **Las Vegas under a feasibility promise.** On every feasible instance a second algorithm has expected running time at most $C\,(m+n)$ and every halting run reports a valid pair of vertex-disjoint shortest paths.
--
--   This is the linear-time two disjoint shortest paths theorem (formal version of Theorem 1.2). For the DAG case it covers negative weights; for undirected graphs it matches the input size.
--
--   **Formalization Note** The DAG input lists the weights in the real bank (`encodeDSP`); the undirected input lists them as words (`encodeUDSP`). Storage cells are the cells changed from the initial state. The word width is $A\lceil\log_2(n+m+2)\rceil$ and the field is $\mathbb F_{2^{q(n+m)}}$ with $q(N)\le A\lceil\log_2(N+2)\rceil$, $A$ and $q$ chosen with the programs.
--
--   Differences from the source:
--   - reading: "for every constant c > 0, there is a randomized algorithm using expected O(m + n) time" → one constant $C$ (depending only on the weight exponent $b$) serves every $c>0$; the programs, $A$ and $q$ are chosen after $c$; reason: the stronger reading, as in the base goal; field operations cost one step at every field size
--   - reading: positive integer edge weights bounded by $(m+n)^{O(1)}$ → for every $b\in\mathbb N$, weights with $1\le w(e)\le (m+n)^b$; $C$, $A$, $q$ and the programs may depend on $b$; reason: the $O(1)$ is a constant exponent fixed before the algorithm; every real exponent is below a natural one
--   - reading: "using expected O(m + n) time and O(m + n) storage cells" → expected running time at most $C(m+n)$, and at most $C(m+n)$ storage cells on every tape; reason: the sentence does not say whether 'expected' governs storage; the stronger worst-case reading is taken, and the proof's space bound is deterministic (p.33, 'Depth-first execution releases all temporary data')
--   - reading: $\Theta(\log(m+n))$-bit words and $\mathbb F_{2^q}$ with $q=\Theta(\log(m+n))$ → existential $A\ge1$ and $q$ with word width `wordWidth A (n + m)` and $q(N)\le A\lceil\log_2(N+2)\rceil$; reason: upper bounds only, as in the base goal; $A$ is chosen after $b$, so the word-stored weights fit
--   - reading: "Under a feasibility promise, root resampling gives a Las Vegas algorithm with the same expected running time" → for each case a second program which, on every feasible instance, has expected running time at most $C(m+n)$ and outputs a valid solution on every halting run; nothing is required on infeasible instances; reason: a Las Vegas algorithm never errs; the promise restricts the requirement to feasible instances
--   - encoding: undirected graph, its paths, integer weights stored in words; 'storage cells' → `Digraph` with tail/head as the two ends, edge lists admitting a traversal (`IsUPath`), weights in ℕ given as input words (`encodeUDSP`); storage = `spaceUsed` (cells changed from the initial state); reason: Lean conventions; the input itself occupies $O(m+n)$ cells, so counting changed cells changes no $O(m+n)$ bound
--   - encoding: the respective models of Section 2, four distinct terminals, $(m+n)^{-c}$ → the machine `DisjointPathsDAG.Machine` with the base layouts (`encodeDSP` for DAGs, weights in the real bank); `[s₁, t₁, s₂, t₂].Nodup`; `Real.rpow`; reason: Lean conventions; same instances
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 5.12, p.33 (formal version of Theorem 1.2, p.3); Section 2.1, p.6

import Mathlib
import Definitions.Def_DisjointPathsDAG_Graph
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_DisjointPathsDAG_Encoding
import Definitions.Def_DisjointPathsDAG_Supplement_Undirected
import Definitions.Def_DisjointPathsDAG_Supplement_Guarantees

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DisjointPathsDAG.Supplement

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Theorem 5.12 (Linear-time 2-DSP, formal version
of Theorem 1.2), p.33: "Let G have n vertices, m edges, and four distinct terminals. Suppose G is either
a DAG with arbitrary real edge weights, or an undirected graph with positive integer edge weights
bounded by (m + n)O(1). In the respective computational models of Section 2, for every constant c > 0,
there is a randomized algorithm using expected O(m + n) time and O(m + n) storage cells that never
returns an invalid pair, returns no on every infeasible instance, and reports two vertex-disjoint
shortest paths with probability at least 1 − (m + n)−c on every feasible instance. Under a feasibility
promise, root resampling gives a Las Vegas algorithm with the same expected running time."

For every weight exponent `b` there is a constant `C > 0` such that for every `c > 0` there are a
word-width constant `A ≥ 1`, a field-size function `q` with `q(N) ≤ A · ⌈log₂(N + 2)⌉`, and four
programs such that, on every instance with `n` vertices, `m` edges and terminal pairs `(s₁, t₁)`,
`(s₂, t₂)` with `s₁, t₁, s₂, t₂` pairwise distinct, run with words of `A · ⌈log₂(n + m + 2)⌉` bits and
the field `F_{2^{q(n+m)}}`:
1. (DAG, real weights of any sign, parallel edges allowed) the Monte Carlo program has expected running
   time at most `C (m + n)`, uses at most `C (m + n)` storage cells on every tape, never outputs an
   invalid pair, outputs "no" on every infeasible instance and a solution with probability at least
   `1 − (m + n)^(−c)` on every feasible one; on every feasible instance the Las Vegas program has
   expected running time at most `C (m + n)` and every halting run outputs a solution;
2. (undirected graph, integer weights `1 ≤ w(e) ≤ (m + n)^b` stored in words) the same two guarantees
   for two vertex-disjoint shortest undirected paths.

**Formalization Note** The machine is `DisjointPathsDAG.Machine`; the DAG input is `encodeDSP` (weights
in the real bank), the undirected input is `encodeUDSP` (weights as words). Storage cells are
`spaceUsed` (cells changed from the initial state). `b` comes first since the `O(1)` exponent of the
weight bound may enter the constant; `C` is chosen before the error exponent `c`; the programs, `A`
and `q` are uniform in `n`, `m` and the instance. `(m + n)^(−c)` is `Real.rpow`. The Las Vegas clause is
required only on feasible instances (the feasibility promise). -/
theorem theorem_5_12 :
    ∀ b : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (A : ℕ) (q : ℕ → ℕ) (Pdag Ldag Pund Lund : Program), 1 ≤ A ∧
        (∀ N : ℕ, q N ≤ A * Nat.clog 2 (N + 2)) ∧
        (∀ (n m : ℕ) (G : Digraph n m) (wt : Fin m → ℝ) (pairs : Fin 2 → Fin n × Fin n),
          G.IsAcyclic →
          [(pairs 0).1, (pairs 0).2, (pairs 1).1, (pairs 1).2].Nodup →
          ReportsWithin 2 Pdag (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs) (C * ((m : ℝ) + n))
            (liftSol (IsDSPSolution G wt pairs)) (DSPFeasible G wt pairs)
            (1 - ((m : ℝ) + n) ^ (-c)) ∧
          (∀ ω : Tape (GaloisField 2 (q (n + m))),
            (spaceUsed (wordWidth A (n + m)) (GaloisField 2 (q (n + m))) Pdag
              (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs) ω : ℝ≥0∞) ≤
              ENNReal.ofReal (C * ((m : ℝ) + n))) ∧
          (DSPFeasible G wt pairs →
            LasVegasWithin 2 Ldag (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
              (encodeDSP (GaloisField 2 (q (n + m))) G wt pairs) (C * ((m : ℝ) + n))
              (liftSol (IsDSPSolution G wt pairs)))) ∧
        (∀ (n m : ℕ) (G : Digraph n m) (wt : Fin m → ℕ) (pairs : Fin 2 → Fin n × Fin n),
          (∀ e, 1 ≤ wt e ∧ wt e ≤ (m + n) ^ b) →
          [(pairs 0).1, (pairs 0).2, (pairs 1).1, (pairs 1).2].Nodup →
          ReportsWithin 2 Pund (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
            (encodeUDSP (GaloisField 2 (q (n + m))) G wt pairs) (C * ((m : ℝ) + n))
            (liftSol (IsUDSPSolution G wt pairs)) (UDSPFeasible G wt pairs)
            (1 - ((m : ℝ) + n) ^ (-c)) ∧
          (∀ ω : Tape (GaloisField 2 (q (n + m))),
            (spaceUsed (wordWidth A (n + m)) (GaloisField 2 (q (n + m))) Pund
              (encodeUDSP (GaloisField 2 (q (n + m))) G wt pairs) ω : ℝ≥0∞) ≤
              ENNReal.ofReal (C * ((m : ℝ) + n))) ∧
          (UDSPFeasible G wt pairs →
            LasVegasWithin 2 Lund (wordWidth A (n + m)) (GaloisField 2 (q (n + m)))
              (encodeUDSP (GaloisField 2 (q (n + m))) G wt pairs) (C * ((m : ℝ) + n))
              (liftSol (IsUDSPSolution G wt pairs)))) := by sorry

end DisjointPathsDAG.Supplement
