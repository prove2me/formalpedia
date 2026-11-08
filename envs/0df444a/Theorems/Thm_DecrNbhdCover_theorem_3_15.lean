-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_15
-- name    : DecrNbhdCover.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:53.608358+00:00
-- url     : https://prove2.me/theorems/0ffee4d8-2977-4edb-9b4d-32635307933d
-- title:
--   Theorem 3.15 — weak ApproxBall, also under Property Q′1: time $\tilde O(n\mu D/(d\epsilon^2))$
-- statement:
--   There is a deterministic algorithm for the weak ApproxBall problem with total update time
--   $$\tilde O\left(n\cdot\mu\cdot\frac{D}{d\epsilon^2}\right).$$
--   It works even if Property Q1 in the definition of the emulator is replaced by the weaker Property Q′1.
--
--   This is the tool that maintains the shells of §7 and the balls of §5.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil$; reason: the input words must fit
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: at all times, for a dynamic $G$ and $H$ and deletions from $S$ → each step is nonempty, has at most one update of $G$ and any updates of $H$ and deletions from $S$, and the promise holds after each step; reason: p.16 indexes $G^{(\tau)},H^{(\tau)}$ by the updates of $G$; $H$-only steps occur when the problem runs on $G[C]$ and $H_C$ (§7)
--   - reading: "Property Q1 in the definition of a proper emulator is replaced" → the promise is a partial emulator, or a partial emulator with Q1 replaced by Q′1, with one program for both; P4 is not assumed; reason: Definition 3.14 and §4, p.30 take a partial emulator
--   - encoding: $S'$ and real values $\tilde d(v)$ → a log of rational values, with monotonicity a clause; reason: a machine writes words
--   - encoding: query time $\tilde O(|E(P)|)$ → $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a path may have no edge, as when $v=v'$ (C.11, p.116)
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
--   - encoding: maximum degree at most $\mu$ → $\mu\ge1$; reason: the printed time bound would be $0$ at $\mu=0$
--   - encoding: the decremental set $S$ and its deletions → a list of the initial vertices of $S$ with no repeated vertex, and per step a list of deleted vertices with no repeated vertex; reason: $S$ is a set, so a vertex occurs in it, and is deleted from it, once
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.15, p.21 (PDF 25); Definition 3.14, p.21 (PDF 25)

import Mathlib
import Definitions.Def_DecrNbhdCover_ApproxBall

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.15.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.21 (PDF 25).

"There is a deterministic algorithm for the weak ApproxBall problem, whose total update time is Õ(n · µ · D/(d·ϵ²)). The algorithm works even if Property Q1 in the definition of a proper emulator is replaced with the following weaker property: Q′1. For every pair v, v′ ∈ V(G) of distinct vertices lying in the same connected component of G, there exists some shortest v-v′ path P in G, together with some vertex a ∈ V(P) \ {v} and a supernode u ∈ U, such that (v, u), (a, u) ∈ E(H), and, additionally: either a = v′ and ℓH(v, u) + ℓH(a, u) ≤ (1 + ϵ) · distG(v, a) + ϵ · D; or a ≠ v′ and ℓH(v, u) + ℓH(a, u) ≤ (1 + ϵ) · distG(v, a)."

**Formalization Note.** One program serves both promises: the partial emulator of Definition 3.14, and the same with Q1 replaced by Q′1. §4 (p.30) proves the theorem for a partial emulator under this replacement, so P4 is not assumed. -/
theorem theorem_3_15 :
    ∃ (C c₀ : ℕ) (P : Program), NoRand P ∧
      ∀ I : BallInput, I.Ok →
        ∀ (W : ℕ) (σ : List BallOp),
          c₀ * Nat.clog 2 (2 + ballProtocol.inputMax I.words σ) ≤ W →
          I.Promise σ →
          ((∀ t ≤ σ.length, IsPartial (I.Gt σ t) (I.Ht σ t).g (I.eps : ℝ) I.d (I.D : ℝ)) ∨
            (∀ t ≤ σ.length, IsPartialQ1' (I.Gt σ t) (I.Ht σ t).g (I.eps : ℝ) I.d (I.D : ℝ))) →
          I.QueriesOk W P σ → BallHolds C W P I σ := by sorry

end DecrNbhdCover
