-- Prove2me | Theorems.Thm_DecrNbhdCover_theorem_3_21
-- name    : DecrNbhdCover.theorem_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:41.705142+00:00
-- url     : https://prove2.me/theorems/32752a02-cd33-4236-9a45-bd183e014be8
-- title:
--   Theorem 3.21 — weak MaintainEmulator: time $O(n^{1+O(\sqrt\epsilon)}(D\mu\mu'/d)^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$, with $H'=H_{G,\mathcal N}$
-- statement:
--   There is a deterministic algorithm for the weak MaintainEmulator problem with total update time
--   $$O\left(n^{1+O(\sqrt\epsilon)}\cdot\left(\frac{D\mu\mu'}{d}\right)^{O(1)}\cdot2^{O(1/\mathrm{poly}(\epsilon))}\right).$$
--   It maintains an $(\epsilon,D,D')$-shelled neighborhood cover $\mathcal N$ for $G$, and the proper $(\epsilon',D,D')$-emulator $H'$ that it maintains is $H'=H_{G,\mathcal N}$, where $\epsilon'=\epsilon+\epsilon^2/2$.
--
--   This is the inductive step of the emulator construction.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_0}\rceil$; reason: the input words must fit, and the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters → rational parameters given by numerator and denominator; reason: a machine reads words; a real value reduces to a nearby rational, with the difference absorbed by the constants
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - reading: "a large enough constant $c$" → $\exists c_0\,\forall c\ge c_0$, with $c$ a parameter of the definitions and $C$ chosen after $c$; reason: $c$ is a universal constant, and the proof of Theorem 3.23 (p.24) chooses its $c$ "sufficiently larger than $c_0$"
--   - reading: at all times, for a dynamic $G$ and $H$ → each step is nonempty, has at most one update of $G$ and any updates of $H$, and the promise holds after each step; reason: p.16 indexes $G^{(\tau)},H^{(\tau)}$ by the updates of $G$; $H$-only steps occur when the problem runs on $G[C]$ and $H_C$ (§7)
--   - encoding: the shelled cover $\mathcal N$ with real $D_S$, $\tilde d_S$ → a log of the update types of §7.4 with rational values, with $D_S$ fixed at creation and an id never reused; reason: a machine writes words
--   - reading: changes of $T(S)$ are not described → additions to and deletions from $T(S)$ are both allowed, as reports; reason: §7 describes updates of $S$ and $\mathrm{Shell}(S)$ and does not restrict $T(S)$; the shelled cover property is required at all times
--   - reading: "maintains $H'$" → $H'$ is the function $H_{G,\mathcal N}$ of $G$ and the reported cover and is not reported again; it is required to be a dynamic well-structured graph; reason: the paper names no machine, so "maintains" fixes no data layout; every update of $H'$ is determined by one of $G$ or of the cover, and the edges of $H'$ ever present number at most $n$ times its dynamic degree bound, which the time bound covers
--   - reading: "path" in query answers → a walk, given by its edge ids; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"; the paper says "simple path" where it means it
--   - encoding: query time $\tilde O(|E(P)|)$ → $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a path may have no edge, as when $v=v'$ (C.11, p.116)
--   - encoding: query time and "total update time" → a window of steps runs from the read of an operation to the read of the next one; query windows are excluded from the total update time and have their own bound; reason: a query never changes the graph
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.21, p.24 (PDF 28); Definition 3.20, p.23 (PDF 27); §7.4, p.61 (PDF 65)

import Mathlib
import Definitions.Def_DecrNbhdCover_MaintainEmulator

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Theorem 3.21.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.24 (PDF 28).

"There is a deterministic algorithm for the weak MaintainEmulator problem with total update time: O(n^(1+O(√ϵ)) · (D · µ · µ′/d)^O(1) · 2^(O(1/poly(ϵ)))). The algorithm maintains an (ϵ, D, D′)-shelled neighborhood cover N for G, and the proper (ϵ′, D, D′)-emulator H′ that it maintains is H′ = H_(G,N)."

**Formalization Note.** The problem (Definition 3.20) has "a large enough constant c", the same one as the shelled cover it maintains, read as `∃ c₀, ∀ c ≥ c₀`. -/
theorem theorem_3_21 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : WeakEmuInput, I.Ok c →
          ∀ (W : ℕ) (σ : List WeakEmuOp),
            c₁ * Nat.clog 2 (2 + weakEmuProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
            I.Promise σ → I.QueriesOk W P σ → WeakEmuHolds c C W P I σ := by sorry

end DecrNbhdCover
