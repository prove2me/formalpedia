-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_9_3
-- name    : DecrNbhdCover.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:37:39.221683+00:00
-- url     : https://prove2.me/theorems/30e91db5-37b2-4b13-9c79-1fe4f243e679
-- title:
--   Theorem 9.3 — one recursive level of the APSP reduction: $\beta_h=(7\alpha(M))^{3h}$, total time $O(M^{(h+2)/b}T(M)(s(M)\log M)^{O(h)})$ (corrected: $\max(1,T(M))$)
-- statement:
--   There is a function $K:\mathbb N\to\mathbb N$ such that for all nondecreasing functions $\alpha,s,T:\mathbb N\to\mathbb N$ there is one deterministic reduction $R$ with the following property, for every $(\alpha,s,T)$-neighborhood-cover algorithm $A$ with constant $C_A$ (Definition 9.1), where $R$ has black-box access to $A$ and $K=K(C_A)$.
--
--   The input is integers $M,b,h$ with $1\le h\le b\le\lceil\log_2M\rceil$ and a graph $G$ that initially has no edges or vertices and undergoes an online sequence of at most $\lceil M^{h/b}\rceil$ updates. Each update is an edge insertion, an edge deletion, an insertion of an isolated vertex, or a deletion of an isolated vertex, and every inserted edge has an integer length in $[1,M^{2(b+1-h)}]$. Let
--   $$\beta_h=(7\alpha(M))^{3h}.$$
--
--   1. A distance query $(u,v)$ returns a value $\hat d$ with $\mathrm{dist}_G(u,v)\le\hat d\le\beta_h\cdot\mathrm{dist}_G(u,v)$, in at most $K\,h\,(\log_2(2+M))^K$ steps.
--   2. A shortest-path query $(u,v)$ with $u\ne v$ returns a (possibly non-simple) $u$-$v$ path $P$ in $G$ of length at most $\beta_h\cdot\mathrm{dist}_G(u,v)$, in at most $K\,h^2(\log_2(2+M))^K(|E(P)|+1)$ steps, or correctly reports that no such path exists, in at most $K\,h\,(\log_2(2+M))^K$ steps.
--   3. The total update time is at most
--   $$K\cdot M^{(h+2)/b}\cdot\max(1,T(M))\cdot\bigl(s(M)\cdot\log_2(2+M)\bigr)^{K h}.$$
--
--   The time of $R$ includes the time of every instance of $A$ that it runs. This theorem is the single level of the recursion by which the paper proves Theorem 9.2.
--
--   Differences from the source:
--   - reading: "The algorithm is additionally given black-box access to an $(\alpha,s,T)$-neighborhood-cover algorithm"; black-box access is not defined → the algorithm is a reduction $R$ on the oracle word RAM of the definition item: $R$ is fixed before the oracle program $A$, can create instances of $A$, send them input words and receive the words they write, and every step of every instance counts in the time of $R$; reason: this is what a black-box reduction is: one program for every oracle, which reaches the oracle only through its input and output; Definition 9.1 makes the algorithm report $\alpha(m)$ and $s(m)$ precisely so that such a user can learn them
--   - reading: the constants of $O(\cdot)$ and $\mathrm{polylog}(\cdot)$ in the conclusion, and those of Definition 9.1 → the oracle meets Definition 9.1 with its own constant $C_A$, and the conclusion holds with the constant $K(C_A)$ for one function $K$ fixed before $\alpha,s,T$, the reduction and the oracle; reason: p.81: "The constants hidden in the bounds of Theorem 9.2 depend only on the constants hidden in the time bounds that Definition 9.1 requires from the neighborhood-cover algorithm"
--   - reading: the algorithm is "deterministic", and no machine is named → the reduction and the oracle are programs with no `rand` instruction on the word RAM of the mission, at unit cost per instruction; reason: a running time needs a machine; this is the reading of the published base goal
--   - encoding: no word size is stated → every word size $W\ge K(C_A)(b+1)\lceil\log_2(2+\text{largest input word}+\alpha(M)+s(M)+T(M))\rceil$, shared by the reduction and the instances of the oracle; reason: edge lengths up to $M^{2(b+1-h)}$ and distances up to $\beta_h$ times them need $O(b\log M+h\log\alpha(M))$ bits, and the oracle is only required to work at word sizes large enough for its own input and bounds
--   - reading: $O(h\cdot\mathrm{polylog}(M))$, $O(h^2|E(P)|\,\mathrm{polylog}(M))$, $(s(M)\log M)^{O(h)}$, and "total update time" → $K\,h(\log_2(2+M))^K$, $K\,h^2(\log_2(2+M))^K(|E(P)|+1)$, $(s(M)\log_2(2+M))^{Kh}$, and the time outside query windows, initialization included; reason: the explicit forms with the constant $K(C_A)$; here $M\ge2$, so $\log_2(2+M)$ and $\log_2M$ differ by a factor of at most $2$
--   - correction: the factor $T(M)$ of the total update time → $\max(1,T(M))$; reason: Definition 9.1 allows $T(M)=0$ for small $M$, and the printed bound is then $0$. Counterexample meeting every assumption: an oracle whose bound function has $T(2)=0$ (possible, since on $m=2$ edges its time bound $C_A(n+0)$ is still positive), $M=2$, $b=h=1$ and no update; the run must still read $M,b,h$
--   - encoding: $\lceil\log M\rceil$, and a graph with "no edges or vertices" → the ceiling of $\log_2M$ for naturals, which forces $M\ge2$; the session starts from the empty vertex set, and an inserted vertex carries a number chosen by the update; reason: p.13: logarithms are to base 2
--   - encoding: abstract graphs, updates and answers → vertices and operations given as words; the $j$-th inserted edge is edge $j$; a distance answer is $\infty$ or a rational; a path answer is "no such path" or a list of edge numbers; reason: a machine reads and writes words; relabeling changes no instance
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 9.3, p.68 (PDF 72); Definition 9.1, p.67 (PDF 71); proof §9.2

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_FullyDynamic
import Definitions.Def_DecrNbhdCover_Supplement_NCAlgorithm
import Definitions.Def_DecrNbhdCover_Supplement_Oracle

set_option autoImplicit false

open DynConnWC
open scoped ENNReal

namespace DecrNbhdCover.Supplement

/-- **Theorem 9.3 (one recursive level).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.68 (PDF 72).

"Theorem 9.3 Let α, s, T : N →N be nondecreasing functions. There exists a deterministic algorithm, whose input consists of integers M, b, h with 1 ≤h ≤b ≤⌈log M⌉, and a graph G that initially has no edges or vertices, and undergoes an online sequence of at most ⌈M^{h/b}⌉ updates. Each update is an edge insertion, an edge deletion, an insertion of an isolated vertex, or a deletion of an isolated vertex, and every inserted edge has an integral length in [1, M^{2(b+1−h)}]. Furthermore, the algorithm is given black-box access to an (α, s, T)-neighborhood-cover algorithm A. The algorithm supports the following queries: approximate distance queries: given a pair u, v ∈V (G) of vertices, return a value d with distG(u, v) ≤d ≤βh · distG(u, v), where βh = (7α(M))^{3h}, in time O(h · polylog(M)); and approximate shortest-path queries: given a pair u, v ∈V (G) of distinct vertices, return a (possibly non-simple) u-v path P in G of length at most βh·distG(u, v), in time O(h^2·|E(P)|·polylog(M)), or correctly report that no such path exists, in time O(h · polylog(M)). The total update time of the algorithm is O(M^{(h+2)/b} · T(M) · (s(M) · log M)^{O(h)})."

**Formalization Note.** The paper names no machine. *Black-box access* is as for Theorem 9.2: the algorithm is a reduction `R` (a `rand`-free program of the word RAM of the mission extended by the oracle instructions `spawn`, `send`, `avail`, `recv` of the definition module), chosen before the oracle program `A` and its constant `C_A`; `R` reaches `A` only by sending input words to instances of `A` and receiving the words they write, and every step of every instance counts in the time of `R`. The constants of the conclusion are `K(C_A)` for one map `K` fixed before `α, s, T`, `R` and `A`. `⌈log M⌉` is `Nat.clog 2 M`, so `M ≥ 2`; the graph starts with no vertices and no edges; an inserted vertex carries a number chosen by the update, and the `j`-th inserted edge is edge `j`. `polylog(M)` is `K·log₂(2+M)^K`; `O(h²·|E(P)|·polylog M)` is `K·h²·log₂(2+M)^K·(|E(P)| + 1)`; a query window's time is bounded per answer and excluded from the total update time, which includes the initialization; `T(M)` is `max(1, T(M))` (Definition 9.1 allows `T(M) = 0` for small `M`, and the printed bound is then `0`, although the run reads its input); `log M` in the time bound is `log₂(2+M)`. Input words: `M`, `b`, `h`. The word size is every `W ≥ K(C_A)·(b+1)·⌈log₂(2 + largest input word + α(M) + s(M) + T(M))⌉`, shared by `R` and the instances of `A`. -/
theorem theorem_9_3 :
    ∃ K : ℕ → ℕ, ∀ (α s T : ℕ → ℕ), Monotone α → Monotone s → Monotone T →
      ∃ R : OProgram, ONoRand R ∧
        ∀ (CA : ℕ) (A : Program), IsNCAlgorithm α s T CA A →
          ∀ (M b h : ℕ), 1 ≤ h → h ≤ b → b ≤ Nat.clog 2 M →
            ∀ (W : ℕ) (σ : List FDOp), FDValid 0 σ →
              fdK σ ≤ ⌈(M : ℝ) ^ ((h : ℝ) / (b : ℝ))⌉₊ →
              (∀ u ∈ fdUpdates σ, ∀ x y ℓ, u = .ins x y ℓ → 1 ≤ ℓ ∧ ℓ ≤ M ^ (2 * (b + 1 - h))) →
              K CA * (b + 1) * Nat.clog 2 (2 + fdProtocol.inputMax [M, b, h] σ + α M + s M + T M) ≤ W →
              ORunsThrough W R A (fdProtocol.blocks [M, b, h] σ) ∧
              APSPQueries (oWOutput W R A (fdProtocol.blocks [M, b, h] σ)) (oWTime W R A (fdProtocol.blocks [M, b, h] σ)) 0 σ
                ((7 * (α M : ℝ)) ^ (3 * h))
                ((K CA : ℝ) * (h : ℝ) * lg (M : ℝ) ^ K CA) ((K CA : ℝ) * (h : ℝ) ^ 2 * lg (M : ℝ) ^ K CA)
                ((K CA : ℝ) * (h : ℝ) * lg (M : ℝ) ^ K CA) ∧
              (fdUpdateTime (oWTime W R A (fdProtocol.blocks [M, b, h] σ)) σ : ℝ) ≤
                (K CA : ℝ) * (M : ℝ) ^ (((h : ℝ) + 2) / (b : ℝ)) * mx1 (T M) *
                  ((s M : ℝ) * lg (M : ℝ)) ^ (K CA * h) := by sorry

end DecrNbhdCover.Supplement
