-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_3_26
-- name    : DecrNbhdCover.Supplement.theorem_3_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:34:14.994565+00:00
-- url     : https://prove2.me/theorems/e9eeaf00-49ef-45c3-b4ba-2b972d516ad9
-- title:
--   Theorem 3.26 — decremental ApproxBall: $d(v)\le(1+\epsilon)\mathrm{dist}_G(v,S)+\epsilon D$, $S^\prime\supseteq B_G(S,D/\epsilon^2)$, time $O(n+m^{1+O(\epsilon)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There are a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$ that undergoes an online sequence of edge deletions, a subset $S\subseteq V(G)$ that undergoes an online sequence of vertex deletions, and parameters $0<\epsilon<1$ and $D>0$. The program maintains a subset $S'\subseteq V(G)$ such that:
--
--   1. At all times $B_G(S,D/\epsilon^2)\subseteq S'$.
--   2. For every $v\in S'$ it maintains a value $d(v)\le C\,D/\epsilon^2$ with
--   $$\mathrm{dist}_G(v,S)\le d(v)\le(1+\epsilon)\,\mathrm{dist}_G(v,S)+\epsilon D.$$
--   3. After initialization vertices may leave $S'$ but none may join it, and as long as $v$ lies in $S'$ the value $d(v)$ does not decrease. Every change is reported.
--   4. A query $v\in S'$ returns a path $P$ in $G$ from $v$ to a vertex of $S$ of length at most $d(v)$, in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--   5. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right)$.
--
--   This is the full version of the paper's Theorem 1.3. It needs no degree bound, and the paper uses it for decremental single-source shortest paths (Theorem 10.1).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon,D$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: $d(v)\le O(D/\epsilon^2)$ → $d(v)\le C\,D/\epsilon^2$; reason: the explicit form of $O$ with the universal constant
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.26, pp.27–28 (PDF 31–32); proof C.8

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Ball

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 3.26 (ApproxBall in decremental graphs).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.27-28 (PDF 31-32).

"Theorem 3.26 (ApproxBall in decremental graphs) There is a deterministic algorithm, whose input consists of an n-vertex and m-edge graph G with integral lengths ℓG(e) > 0 on its edges e ∈E(G), that undergoes an online sequence of edge deletions, a subset S ⊆V (G) of vertices that undergoes an online sequence of vertex deletions, and parameters 0 < ϵ < 1 and D > 0. The algorithm maintains a subset S′ ⊆V (G) of vertices, such that, at all times, BG(S, D/ϵ^2) ⊆S′ holds. Additionally, the algorithm maintains, for every vertex v ∈S′, a value d(v) ≤O(D/ϵ^2) with distG(v, S) ≤d(v) ≤(1 + ϵ)distG(v, S) + ϵ · D. Once the vertex set S′ is initialized, vertices may leave it but no new vertices may join it; every vertex deletion from S′ is explicitly reported by the algorithm. Additionally, for every vertex v ∈V (G), as long as v lies in S′, the value d(v) may not decrease, and every change in d(v) is reported by the algorithm. Lastly, the algorithm supports approximate shortest-path queries: given a vertex v ∈S′, return a path P in G connecting v to a vertex of S of length at most d(v), in time ˜O(|E(P)|). The total update time of the algorithm is O(n + m^{1+O(ϵ)} · 2^{O(1/ poly(ϵ))})."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. `d(v) ≤ O(D/ϵ²)` is `d(v) ≤ C·D/ϵ²`; `m^{1+O(ϵ)}` is `m^{1+Cϵ}`; `G` has `n ≥ 1` vertices. -/
theorem theorem_3_26 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : DBallInput, I.Ok →
        ∀ (W : ℕ) (σ : List DBallOp),
          c₁ * Nat.clog 2 (2 + dballProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Valid W P σ → DBallHolds C W P I σ := by sorry

end DecrNbhdCover.Supplement
