-- Prove2me | Theorems.Thm_CorrelatedRounding_lemma_2
-- name    : CorrelatedRounding.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:48.400198+00:00
-- url     : https://prove2.me/theorems/aded552c-ef1f-41cc-a070-8a84f7a128b6
-- title:
--   Lemma 2 — the probability that some item is still waiting
-- statement:
--   For a draw of Algorithm 1 and every $t\ge0$,
--   $$\Pr\Big[\bigcup_{i=1}^q\Big(\min_k\frac{y_k}{u_{ki}}E_k\ge t\Big)\Big]\le q\,e^{-t}.$$
--   The event says that some item has not yet seen any FC open at time $t$. The integral of this bound against $t$ gives the constant of Theorem 1.
--
--   Differences from the source:
--   - encoding: the event min_k (y_k/u_ki) E_k ≥ t → t lies below every EReal clock of item i; reason: same event, written without a minimum of extended reals
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Lemma 2, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **Lemma 2.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, p.10:
"Under Algorithm 1, Pr[⋃_{i=1}^q (min_k (y_k/u_ki) E_k ≥ t)] ≤ q e^{−t} for all t ≥ 0."

**Formalization Note.** The event `min_k (y_k/u_ki) E_k ≥ t` is written as `t` lying below every `EReal` clock
of item `i`. Items are `Fin q`. -/
theorem lemma_2 {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (t : ℝ) (ht : 0 ≤ t) :
    μ (⋃ i, {ω | ∀ k, (t : EReal) ≤ clock u (fun k' => E k' ω) k i}) ≤
      ENNReal.ofReal (q * Real.exp (-t)) := by sorry

end CorrelatedRounding
