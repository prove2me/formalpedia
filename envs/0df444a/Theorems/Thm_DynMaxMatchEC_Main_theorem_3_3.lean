-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_3_3
-- name    : DynMaxMatchEC.Main.theorem_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:36.339055+00:00
-- url     : https://prove2.me/theorems/13aca154-168d-4ed9-bf75-53c1a1ec5481
-- title:
--   Theorem 3.3 — deterministic O(log n)-block-respecting (z, x)-subgraph system with recourse O(log n) and Õ(x + n/x) worst-case update time
-- statement:
--   Let $128<x<z\le n$ be powers of $2$ with $z\ge1536\,x\log_2 n$. There is a deterministic algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges followed by arbitrary edge insertions and deletions, and maintains a $(z,x)$-subgraph system $(S,U,M)$ for $G$ (Definition 3.1, with one constant $c\ge1$ for all inputs): $m(v)\le z$ for all $v$, $m(v)\ge z-cx\log_2 n$ for $v\in S$, $|N_G(u)\cap U|\le16z$ for $u\in U$, where $m(v)$ counts edges of $M\subseteq E(G)$ at $v$. It is **$\rho$-block-respecting** (Definition 3.2) with blocks of $x$ updates: $(S,U)$ changes only at block ends, and at the beginning of block $B$ the algorithm reports $U_B\subseteq U$ and $S_B\subseteq S$, the vertices moving to $S$ and to $U$ at its end, with $|U_B\cup S_B|\le\rho$. It has **recourse $\rho'$**: after every update at most one edge leaves $M$ and at most $\rho'$ edges enter it, all listed explicitly; here $\rho,\rho'\le C\log_2 n$. Initialization takes $K(m_0+n)(1+\log_2n)^k$ steps and every update
--   $$K\Big(x+\frac nx\Big)(1+\log_2 n)^k$$
--   steps. This is the sparsifier on which both matching algorithms are built.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: a fully dynamic n-vertex graph with m₀ initial edges and the parameters x, z → the words n, x, z, m₀ and an edge list of G₀; for every strategy of edge insertions and deletions; reason: a deterministic algorithm's guarantee against every sequence; an illegal proposal ends the run
--   - encoding: the algorithm maintains (S, U, M), reports U_B, S_B and lists all edges added to or deleted from M → (S, U, M) is read from output records: edge insertions and deletions applied to ∅; the initial S; U_B and S_B written at the beginning of block B, applied at its end; reason: this makes 'the partition changes only at block ends' and 'every change of M is listed' hold by construction
--   - encoding: recourse ρ′: at most one edge removed from M and at most ρ′ inserted after every update → at most one deletion record and at most C·log₂ n insertion records written while processing each update; reason: the record count bounds the number of changes; the algorithm writes exactly its changes
--   - encoding: for some absolute constant c ≥ 1 (Definition 3.1); ρ, ρ′ ≤ O(log n) → ∃ c ≥ 1 and ∃ C, fixed with the program before n, x, z; reason: absolute constants
--   - encoding: maintains a (z, x)-subgraph system at all times → after preprocessing and after every completed update; reason: intermediate machine states are not observable
--   - encoding: Õ(m₀ + n), Õ(x + n/x) → K·(m₀ + n)·(1 + log₂ n)^k and K·(x + n/x)·(1 + log₂ n)^k; reason: the standard meaning of the asymptotic notation
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 16, Theorem 3.3 (with Definitions 3.1 and 3.2, pp. 14 and 16)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring
import Definitions.Def_DynMaxMatchEC_Main_Blocks

open DynBrooks

namespace DynMaxMatchEC.Main

/-- **Theorem 3.3** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 16). There are a
coin-free program, a word-size constant `a`, constants `K, k`, a constant `C` (for
`ρ, ρ′ ≤ C·log₂ n`) and a constant `c ≥ 1` (the constant of Property P2) such that for all integers
`128 < x < z ≤ n` that are powers of `2` with `z ≥ 1536·x·log₂ n`, every initial graph `G₀` on
`Fin n` with `m₀` edges (given as the words `n, x, z`, `m₀` and an edge list), every strategy of
edge insertions and deletions, and every tape: preprocessing completes within
`K·(m₀ + n)·(1 + log₂ n)^k` steps; every delivered update completes within
`K·(x + n/x)·(1 + log₂ n)^k` steps; and after preprocessing and every completed update `t`, with
`(S, U, M)` reported by the program (`sysS`, `sysM`; blocks of `x` updates): `(S, U, M)` is a
`(z, x)`-subgraph system for the current graph with constant `c`; if `t ≥ 1`, update `t` wrote at
most one deletion record and at most `C·log₂ n` insertion records for `M`; and for every block `B`
that has begun, `U_B ⊆ U`, `S_B ⊆ S` at its beginning and `|U_B ∪ S_B| ≤ C·log₂ n`. -/
theorem theorem_3_3 :
    ∃ (P : Program) (a K k : ℕ) (C c : ℝ), CoinFree P ∧ 1 ≤ c ∧
      ∀ (n x z : ℕ), 128 < x → x < z → z ≤ n → (∃ i : ℕ, x = 2 ^ i) → (∃ i : ℕ, z = 2 ^ i) →
        1536 * (x : ℝ) * Real.logb 2 n ≤ z →
        ∀ (G₀ : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
        ∀ (A : Strategy (wordSize a (n * n)) n) (ω : ℕ → BitVec (wordSize a (n * n))),
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ IsEdgeUpdate A).PreprocWithin ω
              ((K : ℝ) * (es.length + n) * (1 + Real.logb 2 n) ^ k) ∧
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ IsEdgeUpdate A).UpdatesCompleteWithin ω
              ((K : ℝ) * ((x : ℝ) + (n : ℝ) / x) * (1 + Real.logb 2 n) ^ k) ∧
          ∀ (t : ℕ) (h : Hist (wordSize a (n * n)) n),
            (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ IsEdgeUpdate A).hist ω t = some h →
              IsSubgraphSystem c z x h.graph (sysS n x h.confs t) (sysM n h.last.output) ∧
              (1 ≤ t → countTag 1 (segment h.confs t) ≤ 1 ∧
                (countTag 0 (segment h.confs t) : ℝ) ≤ C * Real.logb 2 n) ∧
              ∀ j : ℕ, 1 ≤ j → (j - 1) * x ≤ t →
                announced n x 3 h.confs j ⊆ Finset.univ \ sysS n x h.confs ((j - 1) * x) ∧
                announced n x 4 h.confs j ⊆ sysS n x h.confs ((j - 1) * x) ∧
                ((announced n x 3 h.confs j ∪ announced n x 4 h.confs j).card : ℝ) ≤
                  C * Real.logb 2 n := by sorry

end DynMaxMatchEC.Main
