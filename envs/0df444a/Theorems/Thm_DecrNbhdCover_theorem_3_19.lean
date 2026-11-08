-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_19
-- name    : DecrNbhdCover.theorem_3_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:57.166474+00:00
-- url     : https://prove2.me/theorems/c92e0d1e-0845-40b5-9272-1630ccd40494
-- title:
--   Theorem 3.19 — weak MaintainNC: approximation $2^{\mathrm{poly}(1/\epsilon)}$, time $O(|V(G^{(0)})|n^{O(\sqrt\epsilon)}(D\mu/d)^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There is a deterministic algorithm for the weak MaintainNC problem with approximation factor $2^{\mathrm{poly}(1/\epsilon)}$ and total update time
--   $$O\left(|V(G^{(0)})|\cdot n^{O(\sqrt\epsilon)}\cdot\left(\frac{D\mu}{d}\right)^{O(1)}\cdot2^{O(1/\mathrm{poly}(\epsilon))}\right).$$
--
--   Short-path queries return paths in the given partial emulator $H$ with no consecutively repeated regular vertices.
--
--   This algorithm is used both in the proof of Theorem 3.28 and inside §7.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_0}\rceil$; reason: the input words must fit, and the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: at all times, for a dynamic $G$ and $H$ → each step is nonempty, has at most one update of $G$ and any updates of $H$, and the promise holds after each step; reason: p.16 indexes $G^{(\tau)},H^{(\tau)}$ by the updates of $G$; $H$-only steps occur when the problem runs on $G[C]$ and $H_C$ (§7)
--   - encoding: "reports" and "maintains" → a log of report words folded into a state, where an illegal report makes the run fail; reason: a pointer change or a cluster change is a write, so reporting it costs what maintaining it costs
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: query time $\tilde O(|E(P)|)$ → $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a path may have no edge, as when $v=v'$ (C.11, p.116)
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.19, p.23 (PDF 27); Definition 3.18, pp.22–23 (PDF 26–27)

import Mathlib
import Definitions.Def_DecrNbhdCover_NeighborhoodCover

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.19.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.23 (PDF 27).

"There is a deterministic algorithm for the weak MaintainNC problem that achieves approximation factor 2^(poly(1/ϵ)), with total update time: O(|V(G^(0))| · n^(O(√ϵ)) · (D · µ/d)^(O(1)) · 2^(O(1/poly(ϵ))))."

**Formalization Note.** `|V(G^(0))|` is `N₀` and `n` the integral parameter of Definition 3.18. -/
theorem theorem_3_19 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : WeakNCInput, I.Ok →
        ∀ (W : ℕ) (σ : List WeakOp),
          c₁ * Nat.clog 2 (2 + (weakProtocol I.N₀).inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Promise σ → I.QueriesOk W P σ → WeakNCHolds C W P I σ := by sorry

end DecrNbhdCover
