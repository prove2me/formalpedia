-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_10_1
-- name    : DecrNbhdCover.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:38:19.722685+00:00
-- url     : https://prove2.me/theorems/2c96ce42-20ec-479e-a3d5-46e50ed4aa37
-- title:
--   Theorem 10.1 — decremental $(1+\epsilon)$-approximate SSSP in time $O(n+m^{1+O(\epsilon)}2^{O(1/\mathrm{poly}(\epsilon))}\log L)$ (corrected: $\log_2(2+L)$)
-- statement:
--   There are a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$ that undergoes an online sequence of edge deletions, a source vertex $s\in V(G)$, and a parameter $0<\epsilon<1$. Let $L$ be the maximum edge length.
--
--   1. The program maintains, for every vertex $v\in V(G)$, a value $d(v)$ with
--   $$\mathrm{dist}_G(v,s)\le d(v)\le(1+\epsilon)\,\mathrm{dist}_G(v,s).$$
--   2. The value $d(v)$ never decreases, and every change to $d(v)$ is reported.
--   3. A query $v$ with $d(v)<\infty$ returns a $v$-$s$ path $P$ in $G$ of length at most $d(v)$, in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--   4. The total update time is at most
--   $$C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\cdot\log_2(2+L)\right).$$
--
--   This is the full version of the paper's Theorem 1.5: a deterministic decremental single-source shortest-paths algorithm with near-linear total update time, obtained from Theorem 3.26.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - correction: the factor $\log L$ of the total update time → $\log_2(2+L)$; reason: at $L=1$ the printed factor is $0$ and the bound becomes $O(n)$. Counterexample meeting every assumption: unit lengths ($L=1$) and $m=n^2$ parallel or distinct edges; reading the $3m$ input words alone takes more than $C\,n$ steps for large $n$
--   - encoding: a value $d(v)$ that may be $\infty$, maintained for every vertex, with every change reported → every estimate is $\infty$ before any report; a report sets $d(v)$ to a rational or to $\infty$; "never decreases" is stated between consecutive moments with $\infty$ the largest value; reason: the theorem speaks of $d(v)<\infty$, so $\infty$ is a value; a disconnected vertex has $\mathrm{dist}_G(v,s)=\infty$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.1, p.77 (PDF 81); proof §10.1

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_SSSP

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 10.1 (Decremental SSSP).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.77 (PDF 81).

"Theorem 10.1 (Decremental SSSP) There is a deterministic algorithm, whose input consists of an n-vertex and m-edge graph G with integral lengths ℓG(e) > 0 on its edges e ∈E(G), that undergoes an online sequence of edge deletions, a source vertex s ∈V (G), and a parameter 0 < ϵ < 1. The algorithm maintains, for every vertex v ∈V (G), a value d(v) with distG(v, s) ≤d(v) ≤(1 + ϵ)distG(v, s). Over the course of the algorithm, the value d(v) may not decrease, and every change to d(v) is reported by the algorithm. Lastly, the algorithm supports approximate shortest-path queries: given a vertex v ∈V (G) with d(v) < ∞, return a v-s path P in G of length at most d(v), in time ˜O(|E(P)|). The total update time of the algorithm is O(n + m^{1+O(ϵ)} · 2^{O(1/ poly(ϵ))} · log L), where L denotes the maximum edge-length."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. `L` is the largest edge length of the input graph and `log L` is `log₂(2 + L)` (at `L = 1` the printed factor is `0`); `m^{1+O(ϵ)}` is `m^{1+Cϵ}`; `2^{O(1/poly(ϵ))}` is `2^{C/ϵ^C}`. -/
theorem theorem_10_1 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ I : SSSPInput, I.Ok →
        ∀ (W : ℕ) (σ : List SSSPOp),
          c₁ * Nat.clog 2 (2 + ssspProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
          I.Valid W P σ → SSSPHolds C W P I σ := by sorry

end DecrNbhdCover.Supplement
