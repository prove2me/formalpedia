-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_2_5
-- name    : DynMaxMatchEC.Main.theorem_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:09.836889+00:00
-- url     : https://prove2.me/theorems/2102d120-a186-458a-a254-2e303edbb98c
-- title:
--   Theorem 2.5 — deterministic block-respecting low-degree set A with O(log n) announced moves per block of δ updates
-- statement:
--   Let $0<\delta<\Delta\le n$ be integers. There is a deterministic algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges and maximum degree at most $\Delta$, then fully dynamic updates keeping every degree at most $\Delta$, and maintains a set $A$ of vertices such that at all times
--   $$\deg_G(v)\le\Delta-2\delta\ \ (v\in A),\qquad \deg_G(v)\ge\Delta-8\delta\ \ (v\notin A).$$
--   The timeline is cut into blocks of exactly $\delta$ updates (the last may be shorter); $A$ changes only at block ends, and at the beginning of each block $B$ the algorithm announces the sets $A^-_B\subseteq A$ and $A^+_B$ (disjoint from $A$) of vertices that leave and join $A$ at its end, with $|A^-_B|+|A^+_B|\le C\log_2 n$. Initialization takes $K(m_0+n)(1+\log_2n)^k$ steps and every update $K\delta(1+\log_2n)^k$ steps, with constants $C,K,k$ and the word size fixed with the program. In §3.2 this algorithm maintains the low-degree set $A$ of the sparsifier $G'$.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: a fully dynamic graph and the parameters δ, Δ, the maximum degree at most Δ at all times → the words n, Δ, δ, m₀ and an edge list of G₀ (any order and orientation); for every strategy whose updates keep every degree at most Δ; reason: a deterministic algorithm's guarantee against every sequence; an illegal proposal ends the run
--   - encoding: the algorithm maintains A and produces A⁻_B, A⁺_B at the beginning of each block → A is read from output records: the initial A in the preprocessing output; A⁻_B, A⁺_B in the output written at the beginning of block B; after t updates A has the moves of the ⌊t/δ⌋ finished blocks applied; reason: this makes 'vertices may only leave or join A at the end of each block' hold by construction
--   - reading: A⁻_B and A⁺_B are the sets of all vertices that will leave or join A → A⁻_B ⊆ A and A⁺_B ∩ A = ∅ at the beginning of B; reason: a vertex can only leave A if it is in A and only join if it is not
--   - encoding: at all times → after preprocessing and after every completed update; reason: intermediate machine states are not observable
--   - encoding: Δ − 2δ and Δ − 8δ → integers (ℤ); reason: Δ − 8δ may be negative
--   - encoding: O(log n), Õ(m₀ + n), Õ(δ) → C·log₂ n, K·(m₀ + n)·(1 + log₂ n)^k and K·δ·(1 + log₂ n)^k with constants fixed with the program; reason: the standard meaning of the asymptotic notation
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 14, Theorem 2.5

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring
import Definitions.Def_DynMaxMatchEC_Main_Blocks

open DynBrooks

namespace DynMaxMatchEC.Main

/-- **Theorem 2.5** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 14). There are a
coin-free program, a word-size constant `a` and constants `K, k, C` such that for all integers
`0 < δ < Δ ≤ n`, every initial graph `G₀` on `Fin n` of maximum degree at most `Δ` with `m₀`
edges (given as the words `n, Δ, δ`, `m₀` and an edge list), every strategy whose updates keep every
degree at most `Δ`, and every tape: preprocessing completes within `K·(m₀ + n)·(1 + log₂ n)^k` steps;
every delivered update completes within `K·δ·(1 + log₂ n)^k` steps; and after preprocessing and
every completed update `t`, with `A` the set reported by the program (blocks of `δ` updates;
`lowSet`): every `v ∈ A` has degree at most `Δ − 2δ`, every `v ∉ A` has degree at least `Δ − 8δ`,
and for every block `B` that has begun, the announced sets satisfy `A⁻_B ⊆ A`, `A⁺_B ∩ A = ∅` (at
the beginning of `B`) and `|A⁻_B| + |A⁺_B| ≤ C·log₂ n`. -/
theorem theorem_2_5 :
    ∃ (P : Program) (a K k C : ℕ), CoinFree P ∧
      ∀ (n Δ δ : ℕ), 0 < δ → δ < Δ → Δ ≤ n →
        ∀ (G₀ : SimpleGraph (Fin n)), MaxDegLE Δ G₀ →
        ∀ (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
        ∀ (A : Strategy (wordSize a (n * n)) n) (ω : ℕ → BitVec (wordSize a (n * n))),
          (Setup.mk P ([n, Δ, δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).PreprocWithin ω
              ((K : ℝ) * (es.length + n) * (1 + Real.logb 2 n) ^ k) ∧
          (Setup.mk P ([n, Δ, δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).UpdatesCompleteWithin ω
              ((K : ℝ) * δ * (1 + Real.logb 2 n) ^ k) ∧
          ∀ (t : ℕ) (h : Hist (wordSize a (n * n)) n),
            (Setup.mk P ([n, Δ, δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).hist ω t = some h →
              (∀ v ∈ lowSet n δ h.confs t, (vdeg h.graph v : ℤ) ≤ (Δ : ℤ) - 2 * δ) ∧
              (∀ v : Fin n, v ∉ lowSet n δ h.confs t → (Δ : ℤ) - 8 * δ ≤ (vdeg h.graph v : ℤ)) ∧
              ∀ j : ℕ, 1 ≤ j → (j - 1) * δ ≤ t →
                announced n δ 1 h.confs j ⊆ lowSet n δ h.confs ((j - 1) * δ) ∧
                Disjoint (announced n δ 2 h.confs j) (lowSet n δ h.confs ((j - 1) * δ)) ∧
                (((announced n δ 1 h.confs j).card + (announced n δ 2 h.confs j).card : ℕ) : ℝ) ≤
                  C * Real.logb 2 n := by sorry

end DynMaxMatchEC.Main
