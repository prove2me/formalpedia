-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_10_4
-- name    : DecrNbhdCover.Supplement.theorem_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:38:51.740811+00:00
-- url     : https://prove2.me/theorems/4b80cd00-a7cc-40ef-bfcf-5ec08cdca253
-- title:
--   Theorem 10.4 — fully dynamic APSP: approximation $2^{1/\mathrm{poly}(\epsilon)}$, amortized update time $O(m^{O(\epsilon)}2^{O(1/\mathrm{poly}(\epsilon))}\log L)$ (corrected: degenerate factors)
-- statement:
--   There are a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex graph $G$ that initially contains no edges and undergoes an online sequence of edge insertions and deletions, where every edge has an integer length $\ell_G(e)>0$, and a parameter $0<\epsilon<1$. Let $m$ be the total number of edges that ever lie in $G$ and $L$ the maximum edge length. The values $m$ and $L$ are not known to the algorithm.
--
--   1. A distance query $(u,v)$ returns an estimate $d_{u,v}$ with
--   $$\mathrm{dist}_G(u,v)\le d_{u,v}\le2^{C/\epsilon^C}\cdot\mathrm{dist}_G(u,v),$$
--   in at most $C(\log_2(2+m))^C$ steps.
--   2. A shortest-path query $(u,v)$ with $u\ne v$ returns a (possibly non-simple) $u$-$v$ path $P$ in $G$ of length at most $2^{C/\epsilon^C}\cdot\mathrm{dist}_G(u,v)$, in at most $C(\log_2(2+m))^C(|E(P)|+1)$ steps, or correctly reports that no such path exists, in at most $C(\log_2(2+m))^C$ steps.
--   3. With $k$ the number of updates, the total time outside query windows is at most
--   $$\max(1,k)\cdot C\cdot\max(1,m)^{C\epsilon}\cdot2^{C/\epsilon^C}\cdot\log_2(2+L).$$
--
--   This is the full version of the paper's Theorem 1.6: deterministic fully dynamic all-pairs shortest paths with constant approximation for constant $\epsilon$ and amortized update time $m^{O(\epsilon)}$. The paper derives it from Theorems 9.2 and 3.29.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil+\lceil(1/\epsilon)^{c_1}\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words; the time budget contains $2^{C/\epsilon^C}$ while a RAM addresses only $2^W$ cells
--   - encoding: real parameters $\epsilon$ → rationals given by numerator and denominator; reason: a machine reads words
--   - encoding: abstract graphs, updates and answers → vertices and operations given as words; the $j$-th inserted edge is edge $j$; a distance answer is $\infty$ or a rational; a path answer is "no such path" or a list of edge numbers; reason: a machine reads and writes words; relabeling changes no instance
--   - reading: "Let $m$ denote the total number of edges that ever lie in $G$, and let $L$ denote the maximum edge-length; the values $m$ and $L$ are not known to the algorithm" → $m$ is the number of insertions and $L$ the largest inserted length of the whole operation sequence, which the program reads online; reason: every edge that ever lies in $G$ is inserted, since $G$ starts with no edges
--   - reading: "amortized update time … per update", $O(\mathrm{polylog}(m))$ and $O(|E(P)|\cdot\mathrm{polylog}(m))$ → the total time outside query windows, initialization included, is at most $\max(1,k)$ times the per-update bound, with $k$ the number of updates; query windows take at most $C(\log_2(2+m))^C$ and $C(\log_2(2+m))^C(|E(P)|+1)$ steps; reason: the meaning of amortized time over the whole sequence, and the explicit form of $\mathrm{polylog}$
--   - correction: the factors $m^{O(\epsilon)}$ and $\log L$ of the amortized bound, and the multiplication by the number of updates → $\max(1,m)^{C\epsilon}$, $\log_2(2+L)$ and $\max(1,k)$; reason: the printed bound is $0$ when a factor vanishes. Counterexample meeting every assumption: a single insertion of an edge of length $1$ ($L=1$, $\log L=0$) costs at least one step; with no update at all ($k=0$, $m=0$) the run still reads $n$ and $\epsilon$
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.4, pp.80–81 (PDF 84–85); proof §10.2

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 10.4 (Fully-Dynamic APSP).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.80-81 (PDF 84-85).

"Theorem 10.4 (Fully-Dynamic APSP) There is a deterministic algorithm that receives as input an n-vertex graph G that initially contains no edges, and that undergoes an online sequence of edge insertions and deletions, where every edge e has an integral length ℓG(e) > 0. The algorithm is additionally given a parameter 0 < ϵ < 1. Let m denote the total number of edges that ever lie in G, and let L denote the maximum edge-length; the values m and L are not known to the algorithm. The algorithm supports two types of queries: approximate distance query: given a pair u, v ∈V (G) of vertices, return a distance estimate du,v with distG(u, v) ≤du,v ≤2^{1/ poly(ϵ)} · distG(u, v), in time O(polylog(m)); and approximate shortest-path query: given a pair u, v ∈V (G) of distinct vertices, return a (possibly non-simple) u-v path P in G of length at most 2^{1/ poly(ϵ)}·distG(u, v) in time O(|E(P)| · polylog(m)), or correctly report that no such path exists, in time O(polylog(m)). The amortized update time of the algorithm is O(m^{O(ϵ)} · 2^{O(1/ poly(ϵ))} · log L) per update."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. Input words: `n`, then `ϵ` as a rational. `m` (the number of edges that ever lie in `G`, i.e. of insertions), `L` (the largest inserted length) and the number `k` of updates are those of the whole sequence. `2^{1/poly(ϵ)}` is `2^{C/ϵ^C}` for both queries; `polylog(m)` is `C·log₂(2+m)^C`; the amortized update time `X` means that the total time outside query windows, initialization included, is at most `max(1, k)·X`, with `X = C·max(1, m)^{Cϵ}·2^{C/ϵ^C}·log₂(2+L)`. The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉ + ⌈(1/ϵ)^{c₁}⌉`. -/
theorem theorem_10_4 :
    ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
      ∀ (n : ℕ) (eps : ℚ), 0 < eps → eps < 1 →
        ∀ (W : ℕ) (σ : List FDOp), FDValid n σ → NoVertexUpd σ →
          c₁ * Nat.clog 2 (2 + fdProtocol.inputMax (n :: ratWords eps) σ) + ⌈(1 / (eps : ℝ)) ^ c₁⌉₊ ≤ W →
          RunsThrough W P (fdProtocol.blocks (n :: ratWords eps) σ) ∧
          APSPQueries (fdProtocol.out W P (n :: ratWords eps) σ) (wTime W P (fdProtocol.blocks (n :: ratWords eps) σ)) n σ
            (expEps C (eps : ℝ))
            ((C : ℝ) * lg (fdInsertions σ : ℝ) ^ C) ((C : ℝ) * lg (fdInsertions σ : ℝ) ^ C)
            ((C : ℝ) * lg (fdInsertions σ : ℝ) ^ C) ∧
          (fdProtocol.updateTime W P (n :: ratWords eps) σ : ℝ) ≤
            mx1 (fdK σ) * ((C : ℝ) * mx1 (fdInsertions σ) ^ ((C : ℝ) * (eps : ℝ)) * expEps C (eps : ℝ) *
              lg (fdL σ : ℝ)) := by sorry

end DecrNbhdCover.Supplement
