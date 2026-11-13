-- Prove2me | Theorems.Thm_DeepQOperator_reply_simulation
-- name    : DeepQOperator.reply_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:06:06.869554+00:00
-- url     : https://prove2.me/theorems/b171a607-9453-4c11-b8a6-82966aa8a951
-- title:
--   E.5: finite-reply protocols are simulated by exact-affine designs with $B$ and $2^B-1$ rows
-- statement:
--   Let $\Omega$ be a seed space and $P$ a measurable scalar-reply protocol with hard reply budget $B$ on an input set $S$.
--   1. If $P$ is fixed, some measurable fixed exact-affine design with $B$ rows makes the same decision as $P$ on every input of $S$ and every seed.
--   2. For every seed, the reply tree truncated at every history that would exceed the budget has at most $2^B-1$ internal nodes.
--   3. For every $P$ (adaptive), some measurable fixed exact-affine design with $2^B-1$ rows makes the same decision as $P$ on every input of $S$ and every seed.
--
--   With (10), the first gives the fixed lower bound and the third the adaptive lower bound of (7), for arbitrary individual scalar quantizers.
--
--   **Formalization Note** An internal node at seed $\omega$ is a history at which a field is asked, whose symbols are in range for the fields that produced them, and whose cost plus the requested length is at most $B$; every finite set of such histories has at most $2^B-1$ elements.
--
--   Differences from the source:
--   - generalization: the family (6) on P_cb → any finite parameter index type and any input set S; reason: the family is an instance
--   - encoding: a reply of length d ≥ 0 bits in an alphabet of size at most 2^d → every asked field has length ≥ 1 and its symbol lies in {0, …, 2^d − 1}; reason: App. A: "A zero-bit reply is constant and can be removed"; an alphabet of size at most 2^d is a subset of {0, …, 2^d − 1}
--   - reading: a fixed design "preselects its whole list of maps, quantizers and lengths from the seed alone" → IsFixed: asking, maps and lengths depend on the history only through its length; the quantizer of a field may also read earlier symbols; reason: App. A lets every quantizer see earlier symbols; reading the preselected quantizer as a function of them gives the larger fixed class, hence the stronger lower bound (the constructed fixed protocol uses quantizers that do not read them)
--   - encoding: "the sum of lengths is at most B on every input and random path" → HardBudgetOn (Pcb m) B: for every θ ∈ P_cb, every seed ω and every number of steps, the charged lengths along the run total at most B; regret is computed from the run with fuel B; reason: same condition; with lengths ≥ 1 the run asks at most B fields
--   - encoding: "has at most 2^B − 1 internal nodes" → every finite set of internal nodes has at most 2^B − 1 elements; reason: equivalent; avoids the cardinality of a possibly infinite set
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.5, p.26 (PDF p.29)

import Mathlib
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol

open MeasureTheory

namespace DeepQOperator

/-- **The simulations of Appendix E.5** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Appendix E.5, p.26, PDF p.29).

1. A fixed `B`-bit scalar protocol has at most `B` informative fields; revealing the exact values of
   those affine maps lets a fixed exact-affine design with `B` rows reproduce every symbol and the
   final action.
2. The reply tree of an adaptive protocol, truncated at every syntactic history that would exceed the
   budget, has at most `2^B - 1` internal nodes.
3. Hence every adaptive hard-`B`-bit protocol is simulated by a fixed exact-affine design with
   `2^B - 1` rows that reproduces the original action on every input.

**Formalization Note.** The statement is for any parameter index type `ι`, input set `S` and seed
space. "Reproduces" is equality of decisions for every `θ ∈ S` and seed `ω`, with the protocol run with
fuel `B`. The simulating designs are measurable (zero-row padding is allowed by `ExactDesign`). The
internal nodes of the truncated tree at seed `ω` are the histories `h` at which a field is asked,
whose symbols are all in range for the fields that produced them, and whose cost plus the requested
length is at most `B` (`IsBudgetNode`); every finite set of such histories has at most `2^B - 1`
elements. -/
theorem reply_simulation {ι : Type} [Fintype ι] (S : Set (ι → ℝ)) (B : ℕ) (Ω : Type)
    [MeasurableSpace Ω] (P : ReplyProtocol ι Ω) :
    (P.IsMeasurable → P.IsFixed → P.HardBudgetOn S B →
      ∃ D : ExactDesign ι Ω B, D.IsMeasurable ∧ ∀ θ ∈ S, ∀ ω, D.decision θ ω = P.decision B θ ω) ∧
    (∀ (ω : Ω) (T : Finset (List ℕ)), (∀ h ∈ T, P.IsBudgetNode ω B h) → T.card ≤ 2 ^ B - 1) ∧
    (P.IsMeasurable → P.HardBudgetOn S B →
      ∃ D : ExactDesign ι Ω (2 ^ B - 1), D.IsMeasurable ∧
        ∀ θ ∈ S, ∀ ω, D.decision θ ω = P.decision B θ ω) := by sorry

end DeepQOperator
