-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_3_27
-- name    : DecrNbhdCover.Supplement.theorem_3_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:35:03.801625+00:00
-- url     : https://prove2.me/theorems/3a84adef-9c54-4d6d-8f15-33444de6496f
-- title:
--   Theorem 3.27 — MaintainCluster in decremental graphs: bit $g_B$ with a far pair, paths of length $2^{1/\mathrm{poly}(\epsilon)}D$ in $G$, time $O(n+m^{1+O(\epsilon)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There are a constant $C$ and one deterministic program with the following property. The input is a graph $G$ with integer lengths $\ell_G(e)>0$ that initially has $n$ vertices and $m$ edges and undergoes an online sequence of edge deletions and vertex deletions, and parameters $0<\epsilon<1$ and $D>0$. The updates arrive in batches. The first batch $B_0=\emptyset$ arrives at the beginning, and all later batches are non-empty.
--
--   1. After each batch $B$ the program returns a bit $g_B\in\{0,1\}$, and if $g_B=0$ it also returns two vertices $v,v'\in V(G)$ with $\mathrm{dist}_G(v,v')>D$.
--   2. A short-path query $(v,v')$ with $v,v'\in V(G)$ returns a $v$-$v'$ path $P$ in $G$ of length at most
--   $$2^{C/\epsilon^C}\cdot D,$$
--   in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps. A query may be asked only if the program returned $g_B=1$ after the most recent batch, and not before $B_0$ is processed.
--   3. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right)$.
--
--   This variant of the weak MaintainCluster problem needs no emulator and no degree bound, and answers with paths in $G$. The paper uses it in its $k$-PLDD algorithm (Theorem 3.31).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon,D$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - encoding: the bit $g_B$ and the pair $v,v'$ are "returned" → the window of a batch outputs exactly `1`, or `0, v, v′` with $v,v'$ current vertices and $\mathrm{dist}_G(v,v')>D$ in the current graph, where the distance may be $\infty$; reason: the published format of the weak MaintainCluster problem; nothing is required of the bit beyond what the theorem states
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.27, p.28 (PDF 32); proof C.9

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Cluster

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 3.27 (MaintainCluster in decremental graphs).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.28 (PDF 32).

"Theorem 3.27 (MaintainCluster in decremental graphs) There is a deterministic algorithm, whose input consists of a graph G with integral lengths ℓG(e) > 0 on its edges e ∈E(G) that initially has n vertices and m edges, and that undergoes an online sequence of edge deletions and vertex deletions, as well as parameters 0 < ϵ < 1 and D > 0. The updates to graph G arrive in batches, where the first batch, B0 = ∅, arrives immediately at the beginning of the algorithm; all subsequent batches must be non-empty. After each batch B of updates, the algorithm returns a bit gB ∈{0, 1}, and, if gB = 0, it also returns a pair v, v′ ∈V (G) of vertices with distG(v, v′) > D. Lastly, the algorithm supports short-path queries: given a pair v, v′ ∈V (G) of vertices, return a v-v′ path P of length at most 2^{1/ poly(ϵ)} · D in G, in time ˜O (|E(P)|). A short-path query may only be asked if the algorithm returned gB = 1 following the most recent batch B of updates to G, and it cannot be asked before the first batch B0 is processed. The total update time of the algorithm is O(n + m^{1+O(ϵ)} · 2^{O(1/ poly(ϵ))})."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. The path bound `2^{1/poly(ϵ)}·D` is `2^{C/ϵ^C}·D`; `m^{1+O(ϵ)}` is `m^{1+Cϵ}`; `G` has `n ≥ 1` vertices. The theorem does not require the bit `1` when the diameter is small, and none is required here. -/
theorem theorem_3_27 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : CBInput, I.Ok →
        ∀ (W : ℕ) (σ : List CBOp),
          c₁ * Nat.clog 2 (2 + cbProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Valid W P σ → CBHolds C W P I σ := by sorry

end DecrNbhdCover.Supplement
