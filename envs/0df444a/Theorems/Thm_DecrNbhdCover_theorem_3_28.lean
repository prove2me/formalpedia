-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_28
-- name    : DecrNbhdCover.theorem_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:27.462537+00:00
-- url     : https://prove2.me/theorems/6b6d0938-bd3b-44e0-8a2d-5dca7380dd9c
-- title:
--   Theorem 3.28 — strong MaintainNC: approximation $2^{\mathrm{poly}(1/\epsilon)}$, time $O(n^{1+O(\sqrt\epsilon)}\mu^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There is a deterministic path-reporting algorithm for the strong MaintainNC problem with approximation factor $\alpha=2^{\mathrm{poly}(1/\epsilon)}$ and total update time
--   $$O\left(n^{1+O(\sqrt\epsilon)}\cdot\mu^{O(1)}\cdot2^{O(1/\mathrm{poly}(\epsilon))}\right).$$
--
--   So on a decremental graph with $D$ in the problem's range, the algorithm keeps every ball $B_G(v,D)$ inside a pointed cluster, each vertex in at most $\max\{n^\epsilon,4\log n\}$ clusters over the run, and answers short-path queries in $G$ of length at most $\alpha D$.
--
--   This is the algorithm to which Theorem 3.29 reduces.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_0}\rceil$; reason: the input words must fit, and the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: "a large enough constant $c$" → $\exists c_0\,\forall c\ge c_0$, with $c$ a parameter of the definitions and $C$ chosen after $c$; reason: $c$ is a universal constant, and the proof of Theorem 3.23 (p.24) chooses its $c$ "sufficiently larger than $c_0$"
--   - encoding: "reports" and "maintains" → a log of report words folded into a state, where an illegal report makes the run fail; reason: a pointer change or a cluster change is a write, so reporting it costs what maintaining it costs
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: query time $\tilde O(|E(P)|)$ → $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a path may have no edge, as when $v=v'$ (C.11, p.116)
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.28, p.28 (PDF 32); Definition 3.18, pp.22–23 (PDF 26–27)

import Mathlib
import Definitions.Def_DecrNbhdCover_NeighborhoodCover

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.28.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.28 (PDF 32).

"There is a deterministic path-reporting algorithm for the strong MaintainNC problem that achieves approximation factor 2^(poly(1/ϵ)), and has total update time: O(n^(1+O(√ϵ)) · µ^O(1) · 2^(O(1/poly(ϵ))))."

**Formalization Note.** The problem (Definition 3.18) has "a large enough universal constant c", read as `∃ c₀, ∀ c ≥ c₀`. -/
theorem theorem_3_28 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : StrongNCInput, I.Ok c →
          ∀ (W : ℕ) (σ : List GOp),
            c₁ * Nat.clog 2 (2 + (gProtocol I.N₀).inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
            I.Valid W P σ → StrongNCHolds C W P I σ := by sorry

end DecrNbhdCover
