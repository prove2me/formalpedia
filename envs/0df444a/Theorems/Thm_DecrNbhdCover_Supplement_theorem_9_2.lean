-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_9_2
-- name    : DecrNbhdCover.Supplement.theorem_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:36:47.062035+00:00
-- url     : https://prove2.me/theorems/e9322c08-d943-437f-b95e-cc04a2fc107c
-- title:
--   Theorem 9.2 — fully dynamic APSP from a black-box neighborhood cover: $\beta=3(7\alpha(6k))^{3b}$, amortized time $O(k^{2/b}T(6k)(s(6k)\log k)^{O(b)}\log L)$ (corrected: degenerate factors)
-- statement:
--   There is a function $K:\mathbb N\to\mathbb N$ such that for all nondecreasing functions $\alpha,s,T:\mathbb N\to\mathbb N$ there is one deterministic reduction $R$ with the following property, for every $(\alpha,s,T)$-neighborhood-cover algorithm $A$ with constant $C_A$ (Definition 9.1), where $R$ has black-box access to $A$ and $K=K(C_A)$.
--
--   The input is an integer $b\ge1$ and an $n$-vertex graph $G$ with positive integer edge lengths that initially contains no edges and undergoes an online sequence of edge insertions and deletions. Let $k$ be the total number of updates, $L$ the largest length of an edge ever inserted, and
--   $$\beta=3\cdot(7\max(1,\alpha(6k)))^{3b},$$
--   which is the paper's $3\cdot(7\alpha(6k))^{3b}$ except when $k=0$ and $\alpha(0)=0$ (see the last difference below). The values $k$ and $L$ are not known to the algorithm.
--
--   1. A distance query $(u,v)$ returns a value $\hat d$ with $\mathrm{dist}_G(u,v)\le\hat d\le\beta\cdot\mathrm{dist}_G(u,v)$, in at most $K(\log_2(2+k))^K$ steps.
--   2. A shortest-path query $(u,v)$ with $u\ne v$ returns a (possibly non-simple) $u$-$v$ path $P$ in $G$ of length at most $\beta\cdot\mathrm{dist}_G(u,v)$, in at most $K(\log_2(2+k))^K(|E(P)|+1)$ steps, or correctly reports that no such path exists, in at most $K(\log_2(2+k))^K$ steps.
--   3. The total time outside query windows is at most $\max(1,k)\cdot X$, where
--   $$X=K\cdot\max(1,k)^{2/b}\cdot\max(1,T(6k))\cdot\bigl(\max(1,s(6k))\cdot\log_2(2+k)\bigr)^{K b}\cdot\log_2(2+L).$$
--
--   The time of $R$ includes the time of every instance of $A$ that it runs. This is the paper's black-box reduction from fully dynamic all-pairs shortest paths to decremental neighborhood cover; with Theorem 3.29 as the oracle it gives Theorem 10.4.
--
--   Differences from the source:
--   - reading: "The algorithm is additionally given black-box access to an $(\alpha,s,T)$-neighborhood-cover algorithm"; black-box access is not defined → the algorithm is a reduction $R$ on the oracle word RAM of the definition item: $R$ is fixed before the oracle program $A$, can create instances of $A$, send them input words and receive the words they write, and every step of every instance counts in the time of $R$; reason: this is what a black-box reduction is: one program for every oracle, which reaches the oracle only through its input and output; Definition 9.1 makes the algorithm report $\alpha(m)$ and $s(m)$ precisely so that such a user can learn them
--   - reading: the constants of $O(\cdot)$ and $\mathrm{polylog}(\cdot)$ in the conclusion, and those of Definition 9.1 → the oracle meets Definition 9.1 with its own constant $C_A$, and the conclusion holds with the constant $K(C_A)$ for one function $K$ fixed before $\alpha,s,T$, the reduction and the oracle; reason: p.81: "The constants hidden in the bounds of Theorem 9.2 depend only on the constants hidden in the time bounds that Definition 9.1 requires from the neighborhood-cover algorithm"
--   - reading: the algorithm is "deterministic", and no machine is named → the reduction and the oracle are programs with no `rand` instruction on the word RAM of the mission, at unit cost per instruction; reason: a running time needs a machine; this is the reading of the published base goal
--   - encoding: no word size is stated → every word size $W\ge K(C_A)(b+1)\lceil\log_2(2+\text{largest input word}+k+\alpha(6k)+s(6k)+T(6k))\rceil$, shared by the reduction and the instances of the oracle; reason: the reduction handles numbers up to $\beta$ times a distance, which needs $O(b\log\alpha(6k))$ bits, and the oracle is only required to work at word sizes large enough for its own input and bounds
--   - reading: "Let $k$ denote the total number of updates … the values $k$ and $L$ are not known to the algorithm" → $k$, $L$ and $\beta$ are computed from the whole operation sequence, which the reduction reads online; reason: this is how a quantity of the whole run that the algorithm does not know enters a guarantee
--   - reading: "amortized update time" $X$ → the total time outside query windows, initialization included, is at most $\max(1,k)\cdot X$; reason: the meaning of amortized time over the whole sequence; the proof (F.1) charges the work, including restarts, to the updates
--   - reading: $\mathrm{polylog}(k)$ and $O(|E(P)|\cdot\mathrm{polylog}(k))$ → $K(\log_2(2+k))^K$ and $K(\log_2(2+k))^K(|E(P)|+1)$; reason: the explicit form with the constant $K(C_A)$; at $k\le1$ the literal $\log k$ is $0$
--   - correction: the factors $k^{2/b}$, $T(6k)$, $s(6k)$, $\log k$, $\log L$ of the amortized bound → $\max(1,k)^{2/b}$, $\max(1,T(6k))$, $\max(1,s(6k))$, $\log_2(2+k)$, $\log_2(2+L)$; reason: the printed bound is $0$ whenever one factor vanishes. Counterexample meeting every assumption: a single insertion of an edge of length $1$ ($k=1$, $L=1$, so $\log k=\log L=0$) costs at least one step; likewise Definition 9.1 allows $T(6k)=0$ for small $k$ and does not constrain $s(0)$ at $k=0$, where the run still reads $n$ and $b$
--   - encoding: abstract graphs, updates and answers → vertices and operations given as words; the $j$-th inserted edge is edge $j$; a distance answer is $\infty$ or a rational; a path answer is "no such path" or a list of edge numbers; reason: a machine reads and writes words; relabeling changes no instance
--   - encoding: $\beta=3\cdot(7\alpha(6k))^{3b}$ in the bounds $d\le\beta\cdot\mathrm{dist}_G(u,v)$ → $\beta=3\cdot(7\max(1,\alpha(6k)))^{3b}$; reason: the same number whenever an $(\alpha,s,T)$-neighborhood-cover algorithm exists and $k\ge1$, because Definition 9.1 forces $\alpha(m)\ge1$ for every $m\ge1$ (a short-path query between the two ends of an edge needs a path of positive length). The two differ only at $k=0$ with $\alpha(0)=0$, where the graph has no edges and the printed bound reads $d\le0\cdot\infty$ for $u\ne v$, which is undefined on the page and equals $0$ in the extended reals of Lean, so the literal statement would be false there
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 9.2, pp.67–68 (PDF 71–72); Definition 9.1, p.67 (PDF 71); proof F.1

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic
import Definitions.Def_DecrNbhdCover_Supplement_NCAlgorithm
import Definitions.Def_DecrNbhdCover_Supplement_Oracle

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 9.2 (Fully dynamic APSP from decremental neighborhood cover).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.67-68 (PDF 71-72).

"Theorem 9.2 (Fully dynamic APSP from decremental neighborhood cover) Let α, s, T : N →N be any nondecreasing functions. There exists a deterministic algorithm, whose input consists of an integral parameter b ≥1 and an n-vertex graph G with positive integral edge lengths that initially contains no edges, and that undergoes an online sequence of updates consisting of edge insertions and deletions. The algorithm is additionally given black-box access to an (α, s, T)-neighborhood-cover algorithm. Let k denote the total number of updates, let L denote the maximum edge-length of edges that are ever inserted into G, and let β = 3·(7α(6k))^{3b}; the values k and L are not known to the algorithm. The algorithm supports the following queries: approximate distance queries: given a pair u, v ∈V (G) of vertices, return a value d with distG(u, v) ≤d ≤β · distG(u, v), in time polylog(k); and approximate shortest-path queries: given a pair u, v ∈V (G) of distinct vertices, return a (possibly non-simple) u-v path P in G of length at most β · distG(u, v), in time O(|E(P)| · polylog(k)), or correctly report that no such path exists, in time polylog(k). The amortized update time of the algorithm is O(k^{2/b} · T(6k) · (s(6k) · log k)^{O(b)} · log L)."

**Formalization Note.** The paper names no machine. *Black-box access.* The algorithm is a reduction `R`: a program of the word RAM of the mission (`DynConnWC.Program`, no `rand`) extended by the oracle instructions `spawn`, `send`, `avail`, `recv` of the definition module, run against an oracle program `A`. `R` is chosen before `A` and before the constant `C_A` of `A`, it can create instances of `A`, send them input words and receive the words they write, and nothing else of `A` reaches it; every step of every instance counts in the time of `R`. So one reduction serves every `(α, s, T)`-neighborhood-cover algorithm, as the page says (`R` may depend on `α, s, T`, which the page fixes first). An `(α, s, T)`-neighborhood-cover algorithm is a `rand`-free program meeting Definition 9.1 with its own constant `C_A` for the bounds `Õ(·)`, `O(·)` of that definition. The constants of the conclusion are `K(C_A)` for one map `K` fixed before `α, s, T`, `R` and `A`: they depend on the oracle only through `C_A`. *Bounds.* `k`, `L` are the number of updates and the largest inserted length of the whole sequence, so `β = 3·(7α(6k))^{3b}` is computed from the whole sequence; it is written `3·(7·max(1, α(6k)))^{3b}`, which is the same number whenever an `(α, s, T)`-neighborhood-cover algorithm exists and `k ≥ 1` (Definition 9.1 forces `α(m) ≥ 1` for `m ≥ 1`), and differs only at `k = 0` with `α(0) = 0`, where the graph has no edges and the printed bound `d ≤ β·distG(u, v)` reads `d ≤ 0·∞` for `u ≠ v`; `polylog(k)` is `K·log₂(2+k)^K`; a query window's time is bounded per answer and excluded from the update time; a path answer with `|E(P)|` edges takes at most `K·log₂(2+k)^K·(|E(P)| + 1)` steps. The amortized update time `X` means: the total time outside query windows, initialization included, is at most `max(1, k)·X`, with `X = K·max(1,k)^{2/b}·max(1, T(6k))·(max(1, s(6k))·log₂(2+k))^{K·b}·log₂(2+L)`: each `max` and each `log₂(2+·)` replaces a printed factor that vanishes at `k = 0`, at `T(6k) = 0`, at `s(0) = 0`, at `k = 1` or at `L = 1`, where the run still reads its input (Definition 9.1 allows `T(x) = 0` for small `x`, and constrains `s(0)` not at all). Input words: `n`, `b`. The word size is every `W ≥ K(C_A)·(b+1)·⌈log₂(2 + largest input word + k + α(6k) + s(6k) + T(6k))⌉`, shared by `R` and the instances of `A`. -/
theorem theorem_9_2 :
    ∃ K : ℕ → ℕ, ∀ (α s T : ℕ → ℕ), Monotone α → Monotone s → Monotone T →
      ∃ R : OProgram, ONoRand R ∧
        ∀ (CA : ℕ) (A : Program), IsNCAlgorithm α s T CA A →
          ∀ (n b : ℕ), 1 ≤ b →
            ∀ (W : ℕ) (σ : List FDOp), FDValid n σ → NoVertexUpd σ →
              K CA * (b + 1) * Nat.clog 2 (2 + fdProtocol.inputMax [n, b] σ + fdK σ +
                α (6 * fdK σ) + s (6 * fdK σ) + T (6 * fdK σ)) ≤ W →
              ORunsThrough W R A (fdProtocol.blocks [n, b] σ) ∧
              APSPQueries (oWOutput W R A (fdProtocol.blocks [n, b] σ)) (oWTime W R A (fdProtocol.blocks [n, b] σ)) n σ
                (3 * (7 * mx1 (α (6 * fdK σ))) ^ (3 * b))
                ((K CA : ℝ) * lg (fdK σ : ℝ) ^ K CA) ((K CA : ℝ) * lg (fdK σ : ℝ) ^ K CA)
                ((K CA : ℝ) * lg (fdK σ : ℝ) ^ K CA) ∧
              (fdUpdateTime (oWTime W R A (fdProtocol.blocks [n, b] σ)) σ : ℝ) ≤
                mx1 (fdK σ) * ((K CA : ℝ) * mx1 (fdK σ) ^ ((2 : ℝ) / (b : ℝ)) * mx1 (T (6 * fdK σ)) *
                  (mx1 (s (6 * fdK σ)) * lg (fdK σ : ℝ)) ^ (K CA * b) * lg (fdL σ : ℝ)) := by sorry

end DecrNbhdCover.Supplement
