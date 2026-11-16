-- Prove2me | Theorems.Thm_DynStrings_Supplement_theorem_1_2_whp_grammar_size
-- name    : DynStrings.Supplement.theorem_1_2_whp_grammar_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:51:32.668191+00:00
-- url     : https://prove2.me/theorems/9be8e2fa-9099-49d1-a36d-09f4d8b9070d
-- title:
--   Theorem 1.2 — restricted block compression has size $O(\delta\log n)$ with probability at least $1-n^{-c}$
-- statement:
--   Let $S$ be a string of length $n\ge2$ with substring complexity $\delta=\max_{m\ge1}d_m(S)/m$, where $d_m(S)$ is the number of distinct length-$m$ substrings of $S$. Parse $S$ by restricted block compression with random orders as in §4.2, and let size be the run-length straight-line program size of the resulting grammar. For every constant $c>0$ there is a constant $C$, depending only on $c$, such that for every such $S$
--
--   $$\Pr\big[\mathrm{size}>C\,\delta\log n\big]\le n^{-c}.$$
--
--   In words, restricted block compression has size $O(\delta\log n)$ with high probability. Unlike Theorem 1.3, the mission's goal, the statement makes no assumption on the number $\sigma$ of distinct characters (unary strings are included), and it bounds the size by $\delta\log n$ instead of $D$.
--
--   **Formalization Note** The constant $C$ is chosen after $c$ and before the alphabet type, the string and the probability space. The random orders are any family satisfying the published `IsRandomOrders`; `log` is base 2; the bad event is bounded with the outer measure.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet Σ → strings `List α` over an arbitrary type `α` with decidable equality; reason: the statement holds for every alphabet type; taking `α` countably infinite gives the source's statement (the base goal's convention)
--   - encoding: random orders as in §4.2 → any probability space and `ord` with `IsRandomOrders μ ord` (published base definition); reason: the source's assumption on the random orders written for random variables, as in the published goal
--   - encoding: size O(δ log n) with probability at least 1 − n^{−c}, for every constant c > 0 → ∀ c > 0, ∃ C > 0, quantified before the alphabet, the string and the orders: the outer measure of {C·δ·log₂ n < size} is at most n^{−c}; reason: §3, p.14: when a quantity is O(f) w.h.p., the hidden constant may depend on c (and on nothing else)
--   - encoding: the grammar: symbols labelling the nodes of T(S) → the published base `grammar` and its RLSLP `size`; reason: the base mission's published definitions of the parse and its size
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Theorem 1.2, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_DynStrings_Parse
open MeasureTheory ProbabilityTheory

namespace DynStrings.Supplement

open DynStrings

/-- **Theorem 1.2**, p.4.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

Let `S` be a string of length `n ≥ 2` with substring complexity `δ`. For every constant `c > 0`,
restricted block compression of `S` has size `O(δ log n)` with probability at least `1 − n^{−c}`.

**Formalization Note.** The hidden constant `C` depends on `c` only (§3, p.14: "When we state that a
quantity is `O(f)` w.h.p., the hidden constant may depend on `c`"): it is chosen after `c` and before
the alphabet, the string and the probability space. The size is the RLSLP size of the grammar of the
parse (`size`); the random orders are any family satisfying `IsRandomOrders`; `log` is base 2; the
bad event is bounded with the outer measure. There is no hypothesis on the number of distinct
characters (`σ = 1` is included). -/
theorem theorem_1_2_whp_grammar_size :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (α : Type) [DecidableEq α] (S : List α) (Ω : Type) [MeasurableSpace Ω]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (ord : ℕ → Ω → StrSym α → StrSym α → Prop),
        IsRandomOrders μ ord → 2 ≤ S.length →
        μ {ω | C * delta S * Real.logb 2 S.length < (size (fun k => ord k ω) S : ℝ)} ≤
          ENNReal.ofReal ((S.length : ℝ) ^ (-c)) := by sorry

end DynStrings.Supplement
