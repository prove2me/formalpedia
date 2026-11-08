-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_17
-- name    : DecrNbhdCover.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:53.251712+00:00
-- url     : https://prove2.me/theorems/c8a8520f-14a2-40a3-ba7e-ef7337a3a622
-- title:
--   Theorem 3.17 — weak MaintainCluster: approximation $2^{\mathrm{poly}(1/\epsilon)}$, time $O(n^{1+O(\epsilon)}(D\mu/d)^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There is a deterministic algorithm for the weak MaintainCluster problem with approximation factor $2^{\mathrm{poly}(1/\epsilon)}$ and total update time
--   $$O\left(n^{1+O(\epsilon)}\cdot\left(\frac{D\mu}{d}\right)^{O(1)}\cdot2^{O(1/\mathrm{poly}(\epsilon))}\right),$$
--   where $n$ is the initial number of vertices of $G$.
--
--   This is what maintains each cluster in §6.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_0}\rceil$; reason: the input words must fit, and the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: query time $\tilde O(|E(P)|)$ → $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a path may have no edge, as when $v=v'$ (C.11, p.116)
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.17, p.22 (PDF 26); Definition 3.16, p.22 (PDF 26)

import Mathlib
import Definitions.Def_DecrNbhdCover_MaintainCluster

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.17.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.22 (PDF 26).

"There is a deterministic algorithm for the weak MaintainCluster problem, that achieves approximation factor 2^(poly(1/ϵ)) and has total update time O(n^(1+O(ϵ)) · (D·µ/d)^(O(1)) · 2^(O(1/poly(ϵ)))), where n is the initial number of vertices in the input graph G." -/
theorem theorem_3_17 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : ClusterInput, I.Ok →
        ∀ (W : ℕ) (σ : List ClusterOp),
          c₁ * Nat.clog 2 (2 + clusterProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Promise σ → I.QueriesOk W P σ → ClusterHolds C W P I σ := by sorry

end DecrNbhdCover
