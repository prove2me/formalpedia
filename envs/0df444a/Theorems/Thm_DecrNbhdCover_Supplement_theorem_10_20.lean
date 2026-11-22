-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_10_20
-- name    : DecrNbhdCover.Supplement.theorem_10_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:39:54.196282+00:00
-- url     : https://prove2.me/theorems/bb4c2fcb-b00a-4738-a62e-43d6c04b3e84
-- title:
--   Theorem 10.20 — fully dynamic $(O(n),O(\log^2n))$-short cycle decomposition with worst-case update time $n^{o(1)}$
-- statement:
--   There are a function $f:\mathbb N\to\mathbb R$ with $f(n)\to0$, a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex graph $G$ that initially contains no edges and undergoes an online sequence of edge insertions and deletions, where all edge lengths are $1$. After initialization and after every update, the collection of cycles reported by the program is a
--   $$\bigl(C\cdot n,\ C\cdot(\log_2(2+n))^2\bigr)\text{-short cycle decomposition of }G,$$
--   that is, a collection of edge-disjoint cycles of $G$ of length at most $C(\log_2(2+n))^2$ each, such that at most $C\,n$ edges of $G$ lie on no cycle of the collection. Every single update takes at most
--   $$n^{f(n)}$$
--   steps.
--
--   This is the full version of the paper's Theorem 1.8. Short cycle decompositions are a tool for graph sparsification; the bound here is worst-case per update, not amortized.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: $(O(n),O(\log^2n))$ → $(C\,n,\ C(\log_2(2+n))^2)$ with a universal constant $C$; reason: the explicit form of $O$; for $n\ge2$, $\log_2(2+n)\le2\log_2n$, and at $n=1$ the graph has no edges
--   - reading: worst-case update time $n^{o(1)}$ → one function $f$ with $f(n)\to0$, chosen with the program before every input, and at most $n^{f(n)}$ steps in the window of every single update; no bound on the initialization window; reason: worst-case time is a bound on each update, $o(1)$ is a function of $n$ alone, and the theorem bounds only the updates
--   - encoding: "maintains" a decomposition → the program reports each cycle inserted into the collection, with an id and its edge list, and each cycle removed; reason: the collection must be observable; every change is one report
--   - encoding: a graph → a multigraph: parallel edges are allowed and two parallel edges form a cycle of length $2$; reason: §2.1: "By default graphs may contain parallel edges but no self loops"
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.20, p.89 (PDF 93); proof §10.4

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_ShortCycle

set_option autoImplicit false

open DynConnWC
open scoped ENNReal
open Filter Topology

namespace DecrNbhdCover.Supplement

/-- **Theorem 10.20 (Fully dynamic short-cycle decomposition).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.89 (PDF 93).

"Theorem 10.20 (Fully dynamic short-cycle decomposition) There is a deterministic algorithm, whose input consists of an n-vertex graph G that initially contains no edges, and that undergoes an online sequence of edge insertions and deletions (where all edge-lengths are unit). The algorithm maintains an (O(n), O(log^2 n))-short cycle decomposition of G, and its worst-case update time is n^{o(1)}."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input. Input word: `n ≥ 1`; the updates are insertions of unit-length edges and deletions of edges of a multigraph on the vertices `0, …, n-1` (§2.1: graphs may have parallel edges), and there are no queries. The decomposition is the collection reported so far, after initialization and after every update. `(O(n), O(log² n))` is `(C·n, C·log₂(2+n)²)`. The worst-case update time `n^{o(1)}` is `n^{f(n)}` for one function `f → 0` chosen before every input, bounding the window of every single update; the theorem states no bound on the initialization, and none is stated here. (At `n = 1` no update is possible, since there are no self-loops.) The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉`. -/
theorem theorem_10_20 :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ n : ℕ, 1 ≤ n →
          ∀ (W : ℕ) (σ : List FDOp), CycleValid n σ →
            c₁ * Nat.clog 2 (2 + cycleProtocol.inputMax [n] σ) ≤ W →
            RunsThrough W P (cycleProtocol.blocks [n] σ) ∧
            (∀ t ≤ σ.length, ∃ cyc, cycleProtocol.state W P [n] σ t = some cyc ∧
              IsShortCycleDecomposition (fdAt n σ t).g cyc ((C : ℝ) * (n : ℝ)) ((C : ℝ) * lg (n : ℝ) ^ 2)) ∧
            ∀ t < σ.length, (cycleProtocol.opTime W P [n] σ t : ℝ) ≤ (n : ℝ) ^ f n := by sorry

end DecrNbhdCover.Supplement
