-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_3_31
-- name    : DecrNbhdCover.Supplement.theorem_3_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:35:41.052603+00:00
-- url     : https://prove2.me/theorems/d8423173-58b7-4959-bd8b-0967affb5917
-- title:
--   Theorem 3.31 — $k$-PLDD in decremental graphs: path-reporting, approximation $\tilde O(k)$, time $O((n+m^{1+o(1)})k)$
-- statement:
--   There are a function $f:\mathbb N\to\mathbb R$ with $f(m)\to0$, a constant $C$ and one deterministic program that is a path-reporting algorithm for the $k$-PLDD problem (Definition 3.30) with approximation factor
--   $$\alpha=C\cdot k\cdot(\log_2(2+n+m))^C$$
--   and total update time at most
--   $$C\cdot\left(n+m^{1+f(m)}\right)\cdot k.$$
--
--   In detail, the input is an $n$-vertex, $m$-edge graph $G$ with integer lengths $\ell_G(e)>0$ under an online sequence of edge deletions, and integers $k,D>0$. The program maintains $k$ partitions $\Pi_1,\dots,\Pi_k$ of $V(G)$ such that:
--
--   1. for every cluster $C\in\bigcup_i\Pi_i$, at all times, the induced subgraph $G[C]$ has diameter at most $\alpha D$;
--   2. for every vertex $v$, the number of indices $i$ such that at some time $v$ was not $D$-covered by $\Pi_i$ is at most $C\log_2(2+n)$, where $v$ is $D$-covered by $\Pi_i$ if some cluster of $\Pi_i$ contains $B_G(v,D)$;
--   3. after initialization the partitions change only by cluster splitting, and the program lists all vertices of each new cluster;
--   4. a query $(C,v,v')$ with $v,v'\in C\in\bigcup_i\Pi_i$ returns a $v$-$v'$ path $P$ of length at most $\alpha D$, in at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps.
--
--   This is the full version of the paper's Theorem 1.4. Compared with the neighborhood cover of Theorem 3.29 it gives partitions, a bound on the strong diameter, and coverage by all but $O(\log n)$ of the partitions; the paper uses it for its decremental tree cover (Theorem 10.7).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - reading: $O(\cdot)$, $\tilde O(\cdot)$, $\mathrm{poly}(\cdot)$ → one constant $C$ chosen with the program, before every input: $2^{C/\epsilon^C}$ for $2^{1/\mathrm{poly}(\epsilon)}$ and $2^{O(1/\mathrm{poly}(\epsilon))}$, an exponent $C\epsilon$ for $O(\epsilon)$, and $C(\log_2(2+n+m))^C$ for the factor hidden by $\tilde O$; reason: p.81: the hidden constants are universal; p.13: $\tilde O$ hides factors polylogarithmic in the initial $n$ and $m$
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words
--   - encoding: "total update time", and query time $\tilde O(|E(P)|)$ → the steps outside query windows, initialization included; a query window takes at most $C(\log_2(2+n+m))^C(|E(P)|+1)$ steps; reason: a query changes nothing and has its own bound; the $+1$ covers the empty path
--   - encoding: "path" → a walk, given by the list of its edge numbers; reason: p.72: "Recall that paths may be non-simple unless mentioned otherwise"
--   - encoding: abstract graphs, updates and reports → vertices $0,\dots,n-1$ with $n\ge1$, edges numbered by input order, updates and reports given as words and folded into a record in which an illegal report makes the run fail; reason: a machine reads and writes words; relabeling changes no instance, and an empty vertex set has nothing to state
--   - reading: $m^{1+o(1)}$ → one function $f:\mathbb N\to\mathbb R$ with $f(m)\to0$, chosen with the program before every input, and the bound $m^{1+f(m)}$; reason: the proof (§8) fixes $\epsilon$ as a function of $m$ alone, so one algorithm has an exponent that tends to $1$
--   - reading: approximation factor $\tilde O(k)$ → $\alpha=C\,k\,(\log_2(2+n+m))^C$, the same $\alpha$ in the diameter clause and in the query clause; reason: p.13: $\tilde O$ hides factors polylogarithmic in $n$ and $m$; Definition 3.30 uses one $\alpha$
--   - reading: Definition 3.30: the number of indices is "bounded by $O(\log n)$" → at most $C\log_2(2+n)$; reason: the explicit form with the universal constant; at $n=1$ the single vertex is always covered, so both forms give the count $0$
--   - encoding: partitions that change by cluster splitting, with the vertices of $C'$ listed → clusters with ids, created only in the initialization window; afterwards the only legal report is a split listing the vertices moved to a new id; a cluster emptied by a split stays in the record; reason: this is the update the definition allows; an empty cluster affects no clause
--   - encoding: the clauses hold at all times, and the covering clause counts the indices for which $v$ was not $D$-covered "at any time" → the moments after the initialization window and after the window of each operation; reason: the partitions are observable only through the reports, and the reports of one window take effect together. This is the convention of the published base mission
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 3.31, p.30 (PDF 34); Definition 3.30, pp.29–30 (PDF 33–34); proof §8

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_PLDD

set_option autoImplicit false

open DynConnWC
open scoped ENNReal
open Filter Topology

namespace DecrNbhdCover.Supplement

/-- **Theorem 3.31 (k-PLDD in decremental graphs).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.30 (PDF 34).

"Theorem 3.31 (k-PLDD in decremental graphs) There is a deterministic path-reporting algorithm for the k-PLDD problem that achieves approximation factor ˜O(k), and has total update time: O((n + m^{1+o(1)}) · k)."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. `o(1)` is one function `f` of `m` with `f → 0`, chosen before every input (the proof in §8 fixes `ϵ` as a function of `m`). The approximation factor `Õ(k)` is `α = C·k·log₂(2+n+m)^C`, used both for the strong diameter and for the query paths; `O(log n)` of Definition 3.30 is `C·log₂(2+n)` (at `n = 1` both readings force the count `0`, since the one vertex is always covered); `m^{1+o(1)}` is `m^{1+f(m)}`; `G` has `n ≥ 1` vertices. The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉`. -/
theorem theorem_3_31 :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : PLDDInput, I.Ok →
          ∀ (W : ℕ) (σ : List PLDDOp),
            c₁ * Nat.clog 2 (2 + (plddProtocol I.n I.k).inputMax I.words σ) ≤ W →
            I.Valid W P σ → PLDDHolds f C W P I σ := by sorry

end DecrNbhdCover.Supplement
