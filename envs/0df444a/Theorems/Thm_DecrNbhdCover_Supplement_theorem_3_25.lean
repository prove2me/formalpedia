-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_3_25
-- name    : DecrNbhdCover.Supplement.theorem_3_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:33:05.511446+00:00
-- url     : https://prove2.me/theorems/51fdac94-8ea5-4682-839b-77d0080105da
-- title:
--   Theorem 3.25 — strong ApproxBall in time $O(n^{1+O(\epsilon)}\mu^{O(1)}2^{O(1/\mathrm{poly}(\epsilon))})$ (corrected: $\max(1,\mu)$)
-- statement:
--   There is a constant $c_0$ such that for every $c\ge c_0$ there are a constant $C$ and one deterministic program that solves the strong ApproxBall problem (Definition 3.14) with parameter $c$, with total update time at most
--   $$C\cdot n^{1+C\epsilon}\cdot\max(1,\mu)^{C}\cdot2^{C/\epsilon^C}.$$
--
--   In detail, the input is a decremental graph $G$ (edge and vertex deletions) with $n$ vertices initially and maximum degree at most $\mu$, a decremental set $S\subseteq V(G)$, $0<\epsilon<1/400$ and an integer $D$ with $2^{1/\epsilon^{4c}}<D\le2^{1/\epsilon^{16c}}\cdot n\log_2n$. The program maintains a decremental set $S'\subseteq V(G)$ with $B_G(S,10D/\epsilon^2)\subseteq S'$ and, for $v\in S'$, a value $0\le\tilde d(v)\le256D/\epsilon^2$ with $\tilde d(v)\le(1+\epsilon)\,\mathrm{dist}_G(S,v)+\epsilon D$ that never decreases while $v\in S'$. Every change is reported. A query $v\in S'$ returns a path in $G$ from $v$ to a vertex of $S$ of length at most $\tilde d(v)$, in $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps, where $m$ is the initial number of edges.
--
--   The strong problem needs no emulator in its input. The paper obtains it from the weak ApproxBall problem and its emulator algorithm, and uses it for Theorem 3.26.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: Definition 3.14: "for a large enough universal constant $c$" → $\exists c_0\ \forall c\ge c_0$, with the program and $C$ allowed to depend on $c$; reason: the usual meaning of "large enough"; the same reading as the published Theorem 3.28
--   - reading: the theorem says "an algorithm", not "a deterministic algorithm" → a program with no `rand` instruction; reason: p.1: all algorithms in the paper are deterministic, and the weak problem's Theorem 3.15 says so explicitly
--   - correction: the factor $\mu^{O(1)}$ → $\max(1,\mu)^C$; reason: at $\mu=0$ the printed bound is $0$. Counterexample meeting every assumption: a graph with $n\ge2$ vertices and no edges, so maximum degree $0\le\mu=0$, with $S=\emptyset$ and any admissible $\epsilon,D$; the run must still read its input, so its time is positive
--   - encoding: a decremental graph $G$ and a decremental subset $S\subseteq V(G)$ → one operation deletes an edge of $G$, or deletes a vertex of $G$ with its edges (the vertex then also leaves $S$), or deletes a vertex from $S$; reason: $S\subseteq V(G)$ must hold after every update, so a vertex deleted from $G$ cannot stay in $S$. A sequence that first deletes it from $S$ and then from $G$ is allowed as well, so no instance of the page is lost
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.25, p.27 (PDF 31); Definition 3.14, p.21 (PDF 25); proof C.7

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Ball

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 3.25 (strong ApproxBall).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.27 (PDF 31).

"Theorem 3.25 There is an algorithm for the strong ApproxBall problem with total update time O(n^{1+O(ϵ)} · µ^{O(1)} · 2^{O(1/ poly(ϵ))})."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. Definition 3.14's "large enough universal constant c" is read as `∃ c₀, ∀ c ≥ c₀`, as for the published Theorem 3.28. The theorem does not repeat "deterministic", but Definition 3.14 is stated for deterministic algorithms and p.1 says all algorithms of the paper are, so the program has no `rand`. The time bound `O(n^{1+O(ϵ)}·µ^{O(1)}·2^{O(1/poly(ϵ))})` is `C·n^{1+Cϵ}·max(1, µ)^C·2^{C/ϵ^C}`: at `µ = 0` (an edgeless graph, which the definition allows) the printed factor `µ^{O(1)}` is `0`, although the run reads its input. `n ≥ 1`. -/
theorem theorem_3_25 :
    ∃ c₀ : ℕ, ∀ c, c₀ ≤ c →
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : SBallInput, I.Ok c →
          ∀ (W : ℕ) (σ : List SBallOp),
            c₁ * Nat.clog 2 (2 + sballProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
            I.Valid W P σ → SBallHolds C W P I σ := by sorry

end DecrNbhdCover.Supplement
