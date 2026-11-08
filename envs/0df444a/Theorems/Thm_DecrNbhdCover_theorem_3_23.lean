-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_23
-- name    : DecrNbhdCover.theorem_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:52.187955+00:00
-- url     : https://prove2.me/theorems/3c3f4e67-eb22-4bea-91c7-6dbf10b7f69f
-- title:
--   Theorem 3.23 — strong MaintainEmulator: time $O(n^{1+O(\epsilon)}\mu^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There is a deterministic algorithm for the strong MaintainEmulator problem with total update time
--   $$O\left(n^{1+O(\epsilon)}\cdot\mu^{O(1)}\cdot2^{O(1/\mathrm{poly}(\epsilon))}\right).$$
--
--   So on an $n$-vertex graph of maximum degree at most $\mu$ with even lengths and edge deletions, it maintains a well-structured graph $H$ with dynamic degree bound $\tilde O(\mu n^{O(\epsilon)}\mathrm{poly}(1/\epsilon))$ that is a proper and path-transforming $(\epsilon,d,D)$-emulator for $G$.
--
--   This supplies the emulator in the proof of Theorem 3.28.
--
--   **Formalization Note** At $n=1$, $n\log n=0$ makes the range of $d$ empty: the source's own corner.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_0}\rceil$; reason: the input words must fit, and the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: "a large enough constant $c$" → $\exists c_0\,\forall c\ge c_0$, with $c$ a parameter of the definitions and $C$ chosen after $c$; reason: $c$ is a universal constant, and the proof of Theorem 3.23 (p.24) chooses its $c$ "sufficiently larger than $c_0$"
--   - encoding: the maintained graph $H$ → a log of the updates of Definition 3.1 in input format, with the initial $H$ reported in the initialization window; reason: an update is a write, so it costs the same
--   - reading: "there is a deterministic algorithm that supports transform-path queries" → the program that maintains $H$ answers them, in a query window; reason: the queries refer to its own $H$ (Definition 3.2)
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: query time $\tilde O(|E(P')|)$ → $C(\log_2(2+n+m))^C(|E(P')|+1)$ steps; reason: a path may have no edge
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.23, p.24 (PDF 28); Definition 3.22, p.24 (PDF 28)

import Mathlib
import Definitions.Def_DecrNbhdCover_MaintainEmulator

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.23.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.24 (PDF 28).

"There is a deterministic algorithm for the strong MaintainEmulator problem with total update time: O(n^(1+O(ϵ)) · µ^O(1) · 2^(O(1/poly(ϵ))))."

**Formalization Note.** The problem (Definition 3.22) has "a large enough constant c", read as `∃ c₀, ∀ c ≥ c₀`. -/
theorem theorem_3_23 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : StrongEmuInput, I.Ok c →
          ∀ (W : ℕ) (σ : List StrongEmuOp),
            c₁ * Nat.clog 2 (2 + (strongEmuProtocol I.n).inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
            I.Valid W P σ → StrongEmuHolds C W P I σ := by sorry

end DecrNbhdCover
