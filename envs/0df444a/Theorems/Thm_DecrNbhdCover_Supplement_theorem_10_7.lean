-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_10_7
-- name    : DecrNbhdCover.Supplement.theorem_10_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:39:26.263645+00:00
-- url     : https://prove2.me/theorems/2a1b090f-c3ba-4fca-b5a8-62a5cfb2bd19
-- title:
--   Theorem 10.7 — decremental tree cover: $O(\log n\log(Ln))$ dominating tree embeddings with stretch $\tilde O(\log L)$, time $O((m+n)^{1+o(1)}\mathrm{polylog}(L))$ (corrected: degenerate logarithms)
-- statement:
--   There are a function $f:\mathbb N\to\mathbb R$ with $f(x)\to0$, a constant $C$ and one deterministic program with the following property. The input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$ that undergoes an online sequence of edge deletions, where $L$ is the maximum edge length. The program maintains a collection $\mathcal T=\{T_1,\dots,T_k\}$ of
--   $$k\le C\cdot\log_2(2+n)\cdot\log_2(2+L\cdot n)$$
--   graphs with positive integer edge lengths such that, at all times:
--
--   1. for all $1\le i\le k$, the graph $T_i$ is a dominating tree embedding of $G$: a forest with $V(G)\subseteq V(T_i)$ and $\mathrm{dist}_{T_i}(u,v)\ge\mathrm{dist}_G(u,v)$ for all $u,v\in V(G)$;
--   2. for every pair $u,v\in V(G)$ there is an index $1\le i\le k$ with
--   $$\mathrm{dist}_{T_i}(u,v)\le C(\log_2(2+n+m))^C\cdot\log_2(2+L)\cdot\mathrm{dist}_G(u,v).$$
--
--   The total update time is at most $C\cdot(m+n)^{1+f(m+n)}\cdot(\log_2(2+L))^C$.
--
--   This is the full version of the paper's Theorem 1.7. A tree cover lets distance computations in $G$ be replaced by computations in a few trees.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: $(m+n)^{1+o(1)}$ and $\mathrm{polylog}(L)$ → one function $f$ with $f(x)\to0$, chosen with the program before every input, the bound $(m+n)^{1+f(m+n)}$, and $(\log_2(2+L))^C$; reason: one algorithm whose exponent tends to $1$; the proof uses Theorem 3.31, whose parameter depends on the input size alone
--   - reading: $\mathrm{dist}_{T_i}(u,v)\le\tilde O(\mathrm{dist}_G(u,v)\cdot\log L)$, for "some index" → at each moment and for each pair there is an index $i$, which may depend on the pair and the moment, with $\mathrm{dist}_{T_i}(u,v)\le C(\log_2(2+n+m))^C\log_2(2+L)\,\mathrm{dist}_G(u,v)$; reason: p.13 for $\tilde O$; the theorem quantifies the index after the pair
--   - correction: $k=O(\log(n)\cdot\log(L\cdot n))$ and the factor $\log L$ of the stretch → $k\le C\log_2(2+n)\log_2(2+Ln)$ and $\log_2(2+L)$; reason: the printed bounds vanish at degenerate inputs. Counterexample meeting every assumption: the one-vertex graph ($n=1$, $\log n=0$) would need $k=0$ trees, but the pair $(v,v)$ needs an index $1\le i\le k$; and for unit lengths ($L=1$) and two adjacent vertices the stretch bound would be $0<\mathrm{dist}_{T_i}(u,v)$
--   - encoding: a maintained collection of $k$ graphs → $k$ is reported once, and each $T_i$ is a reported dynamic graph that may change by any vertex or edge insertion or deletion; reason: the theorem does not restrict how the $T_i$ change; a tree that is not needed can be the edgeless graph on $V(G)$, which is a dominating tree embedding
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.7 and Definition 10.6, p.82 (PDF 86); proof §10.3

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_TreeCover

set_option autoImplicit false

open DynConnWC
open scoped ENNReal
open Filter Topology

namespace DecrNbhdCover.Supplement

/-- **Theorem 10.7 (Decremental Tree Cover).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.82 (PDF 86).

"Theorem 10.7 (Decremental Tree Cover) There is a deterministic algorithm, whose input consists of an n-vertex and m-edge graph G with integral lengths ℓG(e) > 0 on its edges e ∈E(G), that undergoes an online sequence of edge deletions, where L denotes the maximum edge-length. The algorithm maintains a collection T = {T1, . . . , Tk} of k = O(log(n)·log(L·n)) graphs, with integral lengths ℓT (e) > 0 on the edges of each T ∈T , that satisfy the following properties: for all 1 ≤i ≤k, the graph Ti is a dominating tree embedding of G; and, for every pair u, v ∈V (G) of vertices, there exists some index 1 ≤i ≤k, such that distTi(u, v) ≤ ˜O (distG(u, v) · log L). The total update time of the algorithm is O((m + n)^{1+o(1)} · polylog(L))."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. `o(1)` is one function `f` of `m + n` with `f → 0`, chosen before every input. `k = O(log(n)·log(L·n))` is `k ≤ C·log₂(2+n)·log₂(2+L·n)` (at `n = 1` the printed bound is `0`, although at least one tree is needed); `Õ(distG(u, v)·log L)` is `C·log₂(2+n+m)^C·log₂(2+L)·distG(u, v)`; `polylog(L)` is `log₂(2+L)^C`. `G` has `n ≥ 1` vertices. The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉`. -/
theorem theorem_10_7 :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : TreeInput, I.Ok →
          ∀ (W : ℕ) (σ : List ℕ),
            c₁ * Nat.clog 2 (2 + treeProtocol.inputMax I.words σ) ≤ W →
            I.Valid σ → TreeHolds f C W P I σ := by sorry

end DecrNbhdCover.Supplement
