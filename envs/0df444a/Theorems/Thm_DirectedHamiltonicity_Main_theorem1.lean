-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_theorem1
-- name    : DirectedHamiltonicity.Main.theorem1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:24:40.507436+00:00
-- url     : https://prove2.me/theorems/811fc5a9-a821-44b8-b1fc-291053add8e5
-- title:
--   Theorem 1 — one-sided randomized directed Hamiltonian Cycle in $O(1.9133^n)$ time
-- statement:
--   Directed Hamiltonian Cycle on an $n$-vertex directed graph has a one-sided randomized algorithm with running time $O(1.9133^n)$. Precisely: there is one fixed program $\mathcal A$ of the log-cost RAM with fair coins and a constant $C>0$ such that for every $n\ge0$ and every directed graph on $\{0,\dots,n-1\}$, given by its Boolean adjacency matrix (no symmetry, degree or looplessness assumption):
--
--   1. every run of $\mathcal A$, for every coin string, halts with a one-bit output after total cost at most
--   $$C\cdot1.9133^n;$$
--   2. if the graph has no Hamiltonian cycle, no run outputs "yes" (no false positives);
--   3. if the graph has a Hamiltonian cycle, then for uniformly random coins of any length $L\ge C\cdot1.9133^n$, $\mathcal A$ outputs "yes" with probability at least $2/3$.
--
--   At sizes $n\le1$ the output equals the direct small-size answer on every coin string. Here $1.9133=19133/10000$ exactly. For $n=0$ there is no Hamiltonian cycle; for $n=1$ the answer is the single diagonal entry; a directed 2-cycle is a Hamiltonian cycle for $n=2$. The target is the full one-sided decision result, with no degree or parity promise.
--
--   Differences from the source:
--   - generalization: G a simple loopless directed graph (the convention of §2) → an arbitrary Boolean adjacency matrix on Fin n, loops allowed; at n = 0, 1 the answer is deterministic on every coin string; reason: for n ≥ 2 loops lie on no Hamiltonian cycle, so on simple loopless inputs the statement is the source statement; for n = 1 the cycle is the loop
--   - generalization: running time O(1.9133^n), i.e. at most C·1.9133^n for n ≥ n₀ → total cost at most C·1.9133^n for every n and every coin string; reason: implies the O-bound; finitely many small sizes are absorbed into C
--   - reading: a one-sided randomized algorithm with running time O(1.9133^n) → one fixed program of the published log-cost RAM (TargetedSamplers.Program) that halts within the bound on every coin string, never outputs true on a non-Hamiltonian input, and outputs true with probability ≥ 2/3 on a Hamiltonian input for uniform coins of every length L ≥ the bound; reason: the source fixes no machine model and no success constant; one-sided error with success 2/3 is the convention of its proof (PDF p.5), the log-cost RAM charges bit costs and allows exponential memory, and the time bound is worst case over coin outcomes
--   - encoding: an n-vertex directed graph as input → encodeDigraph n adj: the code of n followed by the n² adjacency bits row by row; reason: a standard encoding of the same graph
-- source:
--   Tomohiro Koana, Soh Kumabe, Breaking the $2^n$ barrier for directed hamiltonicity, STOC 2027 submission #811 (October 2026), source.pdf SHA-256 103ec74bdf635a66ec16e2c21d6fbc0896c1aa986065e20007ae217a701fffb3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/811.pdf, PDF p.2 / printed p.1, Theorem 1 (repeated and proved PDF p.5 / printed p.4)

import Mathlib
import Definitions.Def_DirectedHamiltonicity_Main_Graphs
import Definitions.Def_DirectedHamiltonicity_Main_Algorithms

namespace DirectedHamiltonicity.Main

open Multidigraph

/-- Theorem 1, PDF p.2 / printed p.1 (proof PDF p.5 / printed p.4): Directed Hamiltonian Cycle has a
one-sided randomized algorithm with running time `O(1.9133^n)`. There is one fixed randomized
program `P` of the log-cost RAM and a constant `C > 0` such that for every `n` and every Boolean
adjacency matrix `adj` on `Fin n` (arbitrary directed graph; loops allowed), on the encoded input:

1. every run, for every coin string, halts with a one-bit output after a total cost of at most
   `C · 1.9133^n`;
2. if the graph has no Hamiltonian cycle, no run outputs `true` (no false positives);
3. if it has one, with uniformly random coins of any length `L ≥ C · 1.9133^n` the output is `true`
   with probability at least `2/3`. -/
theorem theorem1 :
    ∃ (P : TargetedSamplers.Program) (C : ℝ), 0 < C ∧
      ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
        (∀ coins : List Bool, ∃ (cost : ℕ) (b : Bool),
          P.RunsIn (runTapes (encodeDigraph n adj) coins) cost (some [b]) ∧
          (cost : ℝ) ≤ C * (19133 / 10000 : ℝ) ^ n) ∧
        (n ≤ 1 → ∀ coins : List Bool,
          P.Outputs (runTapes (encodeDigraph n adj) coins) (some [smallCycleAnswer n adj])) ∧
        (¬ HasHamCycle n adj →
          ∀ coins : List Bool, ¬ P.Outputs (runTapes (encodeDigraph n adj) coins) (some [true])) ∧
        (HasHamCycle n adj → ∀ L : ℕ, C * (19133 / 10000 : ℝ) ^ n ≤ L →
          (2 / 3 : ℝ) ≤ outputProb P (encodeDigraph n adj) L [true]) := by sorry

end DirectedHamiltonicity.Main
