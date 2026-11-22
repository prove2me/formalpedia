-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_5_3
-- name    : DecrNbhdCover.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:36:09.104332+00:00
-- url     : https://prove2.me/theorems/b037efe5-2a99-4d70-a67f-47c094c8b596
-- title:
--   Theorem 5.3 — terminal core: FAIL with $(T_1,T_2,E^\prime)$, or a decremental core $S^\prime$ with $|S^\prime|\ge q/2^{6/\epsilon}$ and paths of length $d\cdot2^{O(1/\epsilon^6)}$
-- statement:
--   There are constants $q_0$, $C$ and one deterministic program with the following property. The input is a connected $n$-vertex graph $G=(V,E,\ell_G)$ with $m_0$ edges, a set $T\subseteq V(G)$ of $q>q_0$ vertices called terminals, and parameters $\epsilon,d,\eta$ with
--   $$\frac{2}{(\log_2 q)^{1/12}}<\epsilon<\frac1{400},\qquad d>1,\qquad \eta>1,$$
--   such that $1/\epsilon$ is an integer. The initialization takes at most $C(\log_2(2+n+m_0))^C\cdot m_0^{1+C\epsilon}\cdot\eta\cdot d^3$ steps and ends in one of two ways.
--
--   **FAIL.** The program returns disjoint $T_1,T_2\subseteq T$ and a set $E'$ of edges of $G$ such that
--   1. $|T_1|=|T_2|$ and $|T_1|\ge q^{1-4\epsilon^3}/4$;
--   2. $|E'|\le d\cdot|T_1|/\eta$;
--   3. $\mathrm{dist}_{G\setminus E'}(t,t')>d$ for all $t\in T_1$, $t'\in T_2$.
--
--   **Otherwise** the program computes an initial set $S\subseteq T$. Then, as $G$ undergoes an online sequence of at most $\Lambda=|T|^{1-11\epsilon}/\eta$ edge deletions, it maintains a decremental subset $S'\subseteq S$ with $|S'|\ge q/2^{6/\epsilon}$ at all times. A query $(x,y)$ with $x,y\in S'$ returns a path $P$ from $x$ to $y$ in the current $G$ of length at most $d\cdot2^{C/\epsilon^6}$, in at most $C(|E(P)|+1)$ steps, and $P$ decomposes into non-empty segments $\sigma_1,\dots,\sigma_r$, each a simple path between two distinct vertices of $T$. The total update time after initialization is at most $C\,n^{1+C\epsilon}$.
--
--   The theorem unifies Corollary 5.3 and Theorem 2.3 of [Chu23] and extends them to general edge lengths. The paper uses it to prove its restricted MaintainCluster theorem (Theorem 5.1).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon,d,\eta$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: "$q$ is greater than a large enough constant" → $q>q_0$ for a constant $q_0$ chosen with the program; reason: the usual meaning of "large enough constant"
--   - reading: "initialization time" and "total update time" are stated separately → the initialization window takes at most $C(\log_2(2+n+m_0))^Cm_0^{1+C\epsilon}\eta d^3$ steps in both outcomes, and the update windows after it take at most $Cn^{1+C\epsilon}$ steps in total; query windows are excluded and take at most $C(|E(P)|+1)$ steps; reason: the theorem gives the two bounds separately, and its query time $O(|E(P)|)$ has no polylogarithmic factor
--   - encoding: "may terminate with a FAIL immediately after initialization … must return", or "computes an initial set $S$" → the initialization window outputs exactly one report, the FAIL witness or the list of $S$; after FAIL nothing more is required; later windows may only report that a vertex leaves $S'$; reason: the two outcomes of the page; a decremental $S'\subseteq S$ changes only by deletions
--   - reading: the path "can be decomposed into a sequence $\sigma_1,\dots,\sigma_r$ of non-empty segments" → the edge list of $P$ is the concatenation of the edge lists of simple paths of the current $G$, each with at least one edge and two distinct terminals as endpoints; for $x=y$ the empty path with $r=0$ is allowed; reason: for $x=y$ the page fixes no path, and the empty path is the shortest answer; for $x\ne y$ the path is non-empty, so $r\ge1$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 5.3, pp.36–37 (PDF 40–41); proof D.2

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_TerminalCore

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 5.3 (terminal core).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.36-37 (PDF 40-41).

"Theorem 5.3 (Follows from Corollary 5.3 and Theorem 2.3 from [Chu23]) There is a deterministic algorithm, whose input consists of a connected n-vertex graph G = (V, E, ℓG(·)), a set T ⊆V (G) of q vertices called terminals, and parameters 2/(log q)^{1/12} < ϵ < 1/400, d > 1 and η > 1, such that 1/ϵ is an integer and q is greater than a large enough constant. The algorithm may terminate with a “FAIL” immediately after initialization, in which case it must return a pair T1, T2 ⊆T of disjoint subsets of terminals, and a set E′ of edges of G, such that: 1. |T1| = |T2| and |T1| ≥ q^{1−4ϵ^3}/4; 2. |E′| ≤ d·|T1|/η; and 3. for every pair t ∈T1, t′ ∈T2 of terminals, distG\E′(t, t′) > d. If the algorithm does not return “FAIL” after initialization, then it computes an initial set S ⊆T of vertices. It then maintains a decremental subset S′ ⊆S of vertices, as G undergoes an online sequence of at most Λ = |T|^{1−11ϵ}/η edge deletions, such that, at all times, |S′| ≥ q/2^{6/ϵ}. The algorithm supports short-path queries between vertices of S′: given a pair x, y ∈S′ of vertices, return a path P connecting x to y in the current graph G, whose length is at most d · 2^{O(1/ϵ^6)}, in time O(|E(P)|); the path P can be decomposed into a sequence σ1, . . . , σr of non-empty segments, where each segment σi is a simple path connecting a pair of distinct vertices of T. The initialization time of the algorithm is ˜O(m0^{1+O(ϵ)} · η · d^3), where m0 is the initial number of edges in G, and its total update time is O(n^{1+O(ϵ)})."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. "q is greater than a large enough constant" is `q > q₀` for a constant `q₀` chosen with the program. The run either outputs "FAIL" with a witness satisfying 1–3 at initialization (and nothing more is required), or outputs `S ⊆ T` and then meets every clause of the continuing run. `Õ(m₀^{1+O(ϵ)}·η·d³)` is `C·log₂(2+n+m₀)^C·m₀^{1+Cϵ}·η·d³`; the total update time `O(n^{1+O(ϵ)})` counts the update windows after initialization; the path length `d·2^{O(1/ϵ⁶)}` is `d·2^{C/ϵ⁶}`; the query time `O(|E(P)|)` is `C·(|E(P)| + 1)`. The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉ + ⌈(1/ϵ)^{c₁}⌉`. -/
theorem theorem_5_3 :
    ∃ (q₀ C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : TCInput, I.Ok q₀ →
        ∀ (W : ℕ) (σ : List TCOp),
          c₁ * Nat.clog 2 (2 + tcProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Valid W P σ →
          InitEnds W P (tcProtocol.blocks I.words σ) ∧
          (wTime W P (tcProtocol.blocks I.words σ) 0 : ℝ) ≤ tcInitBound C I ∧
          ((∃ T₁ T₂ E', tcProtocol.out W P I.words σ 0 = (TCReport.fail T₁ T₂ E').words ∧ I.FailOk T₁ T₂ E') ∨
           (∃ S, tcProtocol.out W P I.words σ 0 = (TCReport.core S).words ∧ (∀ v ∈ S, v ∈ I.T) ∧
              TCHolds C W P I σ)) := by sorry

end DecrNbhdCover.Supplement
