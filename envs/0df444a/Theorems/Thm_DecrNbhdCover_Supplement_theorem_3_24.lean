-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_3_24
-- name    : DecrNbhdCover.Supplement.theorem_3_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:32:24.490886+00:00
-- url     : https://prove2.me/theorems/9ca73136-9aad-491d-b125-b9e48764061a
-- title:
--   Theorem 3.24 — emulator for decremental graphs: $\mathrm{dist}_G\le\mathrm{dist}_H\le(1+\epsilon)\mathrm{dist}_G+\epsilon D$, time $O(n+m^{1+O(\epsilon)}2^{O(1/\mathrm{poly}(\epsilon))})$
-- statement:
--   There is a constant $c_0$ such that for every $c'\ge c_0$ there are a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$ that undergoes an online sequence of edge deletions, and parameters $0<\epsilon<1$ and $0<d<D$ with $D>4d\cdot2^{1/\epsilon^{c'}}$. The program maintains a dynamic graph $H$ with positive edge lengths such that:
--
--   1. $V(G)\subseteq V(H)$ at all times, and all edge lengths of $H$ are integer multiples of a value $d^*$ with $d/C\le d^*\le C\,d$ that is fixed at initialization.
--   2. The number of edges that ever lie in $H$ is at most $C\,m^{1+C\epsilon}$.
--   3. At all times, for all $x,y\in V(G)$,
--   $$\mathrm{dist}_G(x,y)\le\mathrm{dist}_H(x,y)\le(1+\epsilon)\,\mathrm{dist}_G(x,y)+\epsilon D.$$
--   4. Given a (possibly non-simple) path $P$ in $H$ between distinct $x,y\in V(G)$ whose inner vertices all lie in $V(H)\setminus V(G)$, the program returns a (possibly non-simple) path $P'$ in $G$ from $x$ to $y$ with $\ell_G(P')\le\ell_H(P)$ and $|E(P)|\le C(\log_2(2+m))^C\,|E(P')|$, in at most $C(\log_2(2+n+m))^C(|E(P')|+1)$ steps.
--   5. The total update time is at most $C\left(n+m^{1+C\epsilon}\cdot2^{C/\epsilon^C}\right)$.
--
--   This is the paper's emulator theorem, the full version of its Theorem 1.2: a sparse graph with coarse edge lengths that preserves the distances of a decremental graph up to a $(1+\epsilon)$ factor and an additive $\epsilon D$.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon,d,D$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: "for a large enough universal constant $c'$" → $\exists c_0\ \forall c'\ge c_0$, with the program and $C$ allowed to depend on $c'$; reason: the usual meaning of "large enough"; the same reading as the published Theorem 3.28
--   - reading: $d^*=\Theta(d)$ → $d/C\le d^*\le C\,d$; reason: a two-sided bound with a universal constant
--   - reading: the number of edges that ever lie in $H$ "is bounded by $m^{1+O(\epsilon)}$" → at most $C\,m^{1+C\epsilon}$, with a leading constant; reason: the proof (C.6) bounds the number by a constant multiple of $m^{1+O(\epsilon')}$ plus $m$ and absorbs the constant; without the leading constant the bound is not what C.6 proves for small $\epsilon$
--   - reading: $|E(P')|\ge\Omega(|E(P)|/\mathrm{poly}\log m)$ → $|E(P)|\le C(\log_2(2+m))^C|E(P')|$; reason: the explicit form of $\Omega$ and $\mathrm{poly}\log$ with the universal constant
--   - encoding: a dynamic graph $H$ whose lengths are integral multiples of a fixed $d^*$ → $d^*$ is reported once as a positive rational, and $H$ is reported edge by edge with positive integer multipliers; $H$ may change by any vertex or edge insertion or deletion; reason: a value reported once cannot change, and integer multipliers make every length a multiple of it; the theorem does not restrict the updates of $H$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.24, p.27 (PDF 31); proof C.6

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_Emulator

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 3.24 (Emulator for decremental graphs).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.27 (PDF 31).

"Theorem 3.24 (Emulator for decremental graphs.) There is a deterministic algorithm, whose input consists of an n-vertex and m-edge graph G with integral lengths ℓG(e) > 0 on its edges e ∈E(G), that undergoes an online sequence of edge deletions, and parameters 0 < ϵ < 1 and 0 < d < D, such that D > 4d·2^{1/ϵ^{c′}}, for a large enough universal constant c′. The algorithm maintains a dynamic graph H with positive edge lengths, such that V (G) ⊆V (H) holds at all times, and, throughout the algorithm, all edge lengths in H are integral multiples of a value d∗= Θ(d) that remains fixed throughout the algorithm. Moreover, the total number of edges that ever lie in H is bounded by m^{1+O(ϵ)}, and, at all times, for every pair x, y ∈V (G) of vertices, distG(x, y) ≤distH(x, y) ≤(1 + ϵ)distG(x, y) + ϵD holds. Additionally, there is a deterministic algorithm that, given a (possibly non-simple) path P in H connecting a pair x, y ∈V (G) of distinct vertices, such that all inner vertices of P lie in V (H) \ V (G), computes a (possibly non-simple) path P′ in G connecting x to y, with ℓG(P′) ≤ℓH(P) and |E(P′)| ≥Ω(|E(P)|/ poly log m), in time ˜O(|E(P′)|). The total update time of the algorithm is O(n + m^{1+O(ϵ)} · 2^{O(1/ poly(ϵ))})."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. "a large enough universal constant c′" is read as `∃ c₀, ∀ c′ ≥ c₀`. `d* = Θ(d)` is `d/C ≤ d* ≤ C·d`; `Ω(|E(P)|/poly log m)` is `|E(P)| ≤ C·log₂(2+m)^C·|E(P′)|`; `m^{1+O(ϵ)}` (edges ever in `H`) is `C·m^{1+Cϵ}` (the proof in C.6, p.107, absorbs a constant factor into it). `G` has `n ≥ 1` vertices. `H` is reported with integral multipliers of the reported `d*`, so all its lengths are integral multiples of `d*` (see the definition module). The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉ + ⌈(1/ϵ)^{c₁}⌉`. -/
theorem theorem_3_24 :
    ∃ c₀ : ℕ, ∀ c', c₀ ≤ c' →
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : EmuInput, I.Ok c' →
          ∀ (W : ℕ) (σ : List EmuOp),
            c₁ * Nat.clog 2 (2 + emuProtocol.inputMax I.words σ) + ⌈(1 / (I.eps : ℝ)) ^ c₁⌉₊ ≤ W →
            I.Valid W P σ → EmuHolds C W P I σ := by sorry

end DecrNbhdCover.Supplement
