-- Prove2me | Theorems.Thm_DynStrings_theorem_1_3_size_tail_bound
-- name    : DynStrings.theorem_1_3_size_tail_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:47.233539+00:00
-- url     : https://prove2.me/theorems/fada06b2-c0ad-462f-ae22-7f211b8aebcb
-- title:
--   Theorem 1.3 — the size of restricted block compression exceeds $T\ge c_1D$ with probability at most $\exp(-c_2(T/\delta)\log(T/D))$
-- statement:
--   There are absolute constants $c_1,c_2>0$, and an absolute constant $C$ for the second statement, with the following property. Let $S$ be a string of length $n$ with substring complexity $\delta$ and $\sigma\ge2$ distinct characters, and let
--
--   $$D=\delta\,\lg\Big(\frac{n\log\sigma}{\delta\log n}\Big).$$
--
--   Parse $S$ by restricted block compression with random orders as in §4.2. For every $T\ge c_1D$,
--
--   $$\Pr\big[\mathrm{size}>T\big]\le\exp\Big(-c_2\cdot\frac{T}{\delta}\cdot\log\frac{T}{D}\Big),$$
--
--   where size is the run-length straight-line program size of the grammar of $S$. In particular, for every $0<\varepsilon<1$, with probability at least $1-\varepsilon$,
--
--   $$\mathrm{size}\le C\big(D+\delta\lg(1/\varepsilon)\big).$$
--
--   The grammar thus has size $O(D)$ with an exponentially decaying excess, sharp up to $c_2$; this high-probability bound is what a dynamic structure sharing one random choice among all strings needs.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: random total orders ≺_k (even k ≥ 2), paused before active, uniformly random on every fixed finite set of active symbols, independent across rounds → any probability space and `ord` with `IsRandomOrders μ ord`: each realization is a choice of the orders, each `ord k` is measurable, every list of distinct well-formed active symbols is increasing with probability 1/n!, and the rounds are independent; reason: the source's assumption written for random variables; every law satisfying the source's assumption extends to the syntactic symbol type with these properties
--   - encoding: with probability at most / at least 1 − ε → the outer measure of the bad event is at most the bound; reason: the bad-event form does not need measurability of the event
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: the grammar: symbols labelling the nodes of T(S), the unfolding of the root → the unfolding of the symbols of the level word S_{κ(|S|)}; reason: by Fact 4.4 this level word is the single root for non-empty S, and it is empty for the empty string
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Theorem 1.3, p.4

import Mathlib
import Definitions.Def_DynStrings_Parse
open MeasureTheory ProbabilityTheory

namespace DynStrings

/-- **Theorem 1.3**, p.4 (the goal).
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There are absolute constants `c₁, c₂ > 0` (and `C` for the second statement) with the following
property. Let `S` be a string of length `n` with substring complexity `δ` and `σ ≥ 2` distinct
characters, and let `D = δ lg(n log σ / (δ log n))`. For every `T ≥ c₁ D`, restricted block
compression of `S` (with random orders satisfying §4.2) has size larger than `T` with probability
at most `exp(−c₂ (T/δ) log(T/D))`. In particular, for every `0 < ε < 1`, the size is at most
`C (D + δ lg(1/ε))` with probability at least `1 − ε`.

**Formalization Note.** The size is the RLSLP size of the grammar of the parse (`size`). The
random orders are any family satisfying `IsRandomOrders` on any probability space; the constants
are chosen before the alphabet, the string and the probability space. Bad events are bounded with
the outer measure; `log` is base 2. -/
theorem theorem_1_3_size_tail_bound :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (α : Type) [DecidableEq α] (S : List α) (Ω : Type) [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (ord : ℕ → Ω → StrSym α → StrSym α → Prop),
        IsRandomOrders μ ord → 2 ≤ sigma S →
        (∀ T : ℝ, c₁ * Dspace S ≤ T →
          μ {ω | T < (size (fun k => ord k ω) S : ℝ)} ≤
            ENNReal.ofReal (Real.exp (-(c₂ * (T / delta S) * Real.logb 2 (T / Dspace S))))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 →
          μ {ω | C * (Dspace S + delta S * lg (1 / ε)) < (size (fun k => ord k ω) S : ℝ)} ≤
            ENNReal.ofReal ε) := by sorry

end DynStrings
