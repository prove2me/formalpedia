-- Prove2me | Theorems.Thm_DecrNbhdCover_lemma_6_1
-- name    : DecrNbhdCover.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:53.092989+00:00
-- url     : https://prove2.me/theorems/9e4cd720-4278-41c3-92b1-a7dc6602fe38
-- title:
--   Lemma 6.1 — ProcReset: properties R1–R5, time $\tilde O(k^4(|V|+|E|)n^{1/k})$
-- statement:
--   There is a deterministic algorithm ProcReset whose input is a graph $G=(V,E,\ell_G)$, $n\ge2$, $d>0$ and $k\ge2$ with $|V|\le n$ and $k^2$ an integer. It computes clusters $\mathcal C$ of $G$ and, for each $C\in\mathcal C$, a set $T(C)\subseteq C$ and a value $d\le D_C\le d2^{14k^2}$, with properties R1–R5 of the definition: every vertex lies in at most $4k^4n^{2/k^2}$ clusters, and in exactly one $T(C)$; $B_G(v,D_C)\subseteq C$ for $v\in T(C)$; $\mathrm{dist}_C\le D_C$ on $T(C)$, and $\mathrm{dist}_C\le64D_C$ on $C$. Its running time is
--   $$\tilde O\left(k^4(|V|+|E|)n^{1/k}\right).$$
--
--   This is the reset step of the neighborhood cover construction.
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - reading: no word size is stated → every word size $W\ge c_0\lceil\log_2(2+\text{largest input word})\rceil+c_0k^2$; reason: the input words must fit, and a word must be able to hold $D_C$, up to $d2^{14k^2}$
--   - encoding: real $k$ with $k^2$ an integer and real $d$ → the integer $K=k^2$ and a rational $d$ as input words; reason: §6 uses $k=\sqrt{\lceil16/\epsilon\rceil}$, irrational in general
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ with universal constants → one universal constant $C$ chosen before every input: $2^{C/\epsilon^C}$, $n^{C\epsilon}$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81 gives this explicit form for Theorem 3.29, and p.13 says what $\tilde O$ hides
--   - encoding: $n$ vertices → at least one vertex; reason: an empty vertex set has nothing to state, and the printed time bound would be $0$
--   - encoding: the output collection → a word list of clusters with rational $D_C$; reason: a machine writes words; a repeated vertex set counts as two clusters
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Lemma 6.1, p.45 (PDF 49)

import Mathlib
import Definitions.Def_DecrNbhdCover_ProcReset

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Lemma 6.1.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.45 (PDF 49).

"There is a deterministic algorithm, that we refer to as ProcReset, whose input consists of a graph G = (V, E, ℓG(·)) and parameters n ≥ 2, d > 0, and k ≥ 2, such that |V| ≤ n and k² is an integer. The algorithm computes a collection C of clusters of G, and, for every cluster C ∈ C a collection T(C) ⊆ C of vertices, together with a value d ≤ D_C ≤ d·2^(14k²), with the following properties: R1. every vertex of G lies in at most 4k⁴ · n^(2/k²) clusters of C; R2. every vertex v ∈ V lies in exactly one set in {T(C) | C ∈ C}; R3. for every cluster C ∈ C, for every vertex v ∈ T(C), BG(v, D_C) ⊆ C holds; R4. for every cluster C ∈ C, for every pair v, v′ ∈ T(C) of vertices, distC(v, v′) ≤ D_C, and R5. for every cluster C ∈ C, for every pair v, v′ ∈ C of vertices, distC(v, v′) ≤ 64D_C. The running time of the algorithm is Õ(k⁴ · (|V| + |E|) · n^(1/k))."

**Formalization Note.** The input word is `K = k²`. The word size includes `c₀·K`, because a word must be able to hold `D_C`, up to `d·2^(14K)`. `V` is nonempty, since at `|V| = |E| = 0` the printed running time is `0`. -/
theorem lemma_6_1 :
    ∃ (C c₀ : ℕ) (P : Program), NoRand P ∧
      ∀ I : ResetInput, I.Ok →
        ∀ W : ℕ, c₀ * Nat.clog 2 (2 + maxWord I.words) + c₀ * I.K ≤ W →
          RunsThrough W P [I.words] ∧
          (∃ rs, parseWith ResetCluster.words (wOutput W P [I.words] 0) = some rs ∧ ResetOk I rs) ∧
          (wTime W P [I.words] 0 : ℝ) ≤ polylog C I.n I.edges.length *
            ((I.K : ℝ) ^ 2 * ((I.N₀ : ℝ) + (I.edges.length : ℝ)) * (I.n : ℝ) ^ (1 / Real.sqrt (I.K : ℝ))) := by sorry

end DecrNbhdCover
