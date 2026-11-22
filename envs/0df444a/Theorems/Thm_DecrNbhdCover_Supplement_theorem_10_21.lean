-- Prove2me | Theorems.Thm_DecrNbhdCover_Supplement_theorem_10_21
-- name    : DecrNbhdCover.Supplement.theorem_10_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:40:40.338497+00:00
-- url     : https://prove2.me/theorems/b9950181-7b38-4212-bf6e-d80258e8aa51
-- title:
--   Theorem 10.21 — static $(2n,O(\log^2n))$-short cycle decomposition in time $O(m^{1+o(1)}\mathrm{polylog}(n))$ (corrected: $\max(1,m)$)
-- statement:
--   There are a function $f:\mathbb N\to\mathbb R$ with $f(m)\to0$, a constant $C$ and one deterministic static program with the following property. The input is an $n$-vertex, $m$-edge graph $G$ in which all edge lengths are $1$. The program outputs a
--   $$\bigl(2n,\ C\cdot(\log_2(2+n))^2\bigr)\text{-short cycle decomposition of }G,$$
--   that is, a collection of edge-disjoint cycles of $G$ of length at most $C(\log_2(2+n))^2$ each, such that at most $2n$ edges of $G$ lie on no cycle of the collection, in at most
--   $$C\cdot\max(1,m)^{1+f(m)}\cdot(\log_2(2+n))^C$$
--   steps.
--
--   The paper uses this static algorithm to obtain its fully dynamic short-cycle decomposition (Theorem 10.20).
--
--   Differences from the source:
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction, run as an online session of word blocks; reason: a running time needs a machine, and the paper counts ordinary word operations; this is the reading of the published base goal
--   - encoding: no word size is stated → every word size $W\ge c_1\lceil\log_2(2+\text{largest input word})\rceil$, with $c_1$ chosen with the program; reason: input numbers must fit in $O(1)$ words
--   - reading: $O(\log^2n)$, $m^{1+o(1)}$ and $\mathrm{polylog}(n)$ → $C(\log_2(2+n))^2$, one function $f$ with $f(m)\to0$ chosen with the program before every input, and $(\log_2(2+n))^C$; the leftover bound stays exactly $2n$; reason: the explicit forms with a universal constant; $o(1)$ is a function of $m$ alone
--   - correction: the factor $m^{1+o(1)}$ of the running time → $\max(1,m)^{1+f(m)}$; reason: at $m=0$ the printed bound is $0$. Counterexample meeting every assumption: the graph with $n$ vertices and no edges; the run must read its input and write the empty collection, which takes at least one step
--   - encoding: a static algorithm that "computes" a decomposition → a session with no operations: the output of the run on the input words is the list of the cycles, each given by its edge list, and the time is that of the run; reason: a static algorithm reads its input and writes its output
--   - encoding: a graph → a multigraph on the vertices $0,\dots,n-1$ given by its edge list: parallel edges are allowed and two parallel edges form a cycle of length $2$; reason: §2.1: "By default graphs may contain parallel edges but no self loops"
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Theorem 10.21, p.90 (PDF 94); proof §10.4.1

import Mathlib
import Definitions.Def_DecrNbhdCover_Supplement_ShortCycle

set_option autoImplicit false

open DynConnWC
open scoped ENNReal
open Filter Topology

namespace DecrNbhdCover.Supplement

/-- **Theorem 10.21 (static short-cycle decomposition).** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.90 (PDF 94).

"Theorem 10.21 There is a deterministic static algorithm, whose input consists of an n-vertex and m-edge graph G (where all edge-lengths are unit). The algorithm computes a (2n, O(log^2 n))-short cycle decomposition of G in time O(m^{1+o(1)} · polylog(n))."

**Formalization Note.** One program of the published word RAM `DynConnWC.Program` with no `rand` instruction; the constants are chosen before every input; `Õ(·)` hides `C·log₂(2+n+m)^C` in the initial `n, m` (p.13); a query window's time is bounded per answer and excluded from the total update time. A static algorithm is a run on the input alone, with no operations: the output and the time are those of the initialization window. `O(log² n)` is `C·log₂(2+n)²` (for `n ≥ 2` the same up to the constant; at `n ≤ 1` there are no edges). The leftover bound is exactly `2n`. `o(1)` is one function `f` of `m` with `f → 0`, chosen before every input; `m^{1+o(1)}` is `max(1, m)^{1+f(m)}`; `polylog(n)` is `log₂(2+n)^C`. The word size is every `W ≥ c₁⌈log₂(2 + largest input word)⌉`. -/
theorem theorem_10_21 :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∃ (C c₁ : ℕ) (P : Program), NoRand P ∧
        ∀ I : SCInput, I.Ok →
          ∀ W : ℕ, c₁ * Nat.clog 2 (2 + maxWord I.words) ≤ W →
            RunsThrough W P [I.words] ∧
            ∃ cs : List (List ℕ), wOutput W P [I.words] 0 = cycleWords cs ∧
              IsShortCycleDecomposition I.G (fun i => cs[i]?) (2 * (I.n : ℝ)) ((C : ℝ) * lg (I.n : ℝ) ^ 2) ∧
              (wTime W P [I.words] 0 : ℝ) ≤ (C : ℝ) * mx1 I.m ^ (1 + f I.m) * lg (I.n : ℝ) ^ C := by sorry

end DecrNbhdCover.Supplement
