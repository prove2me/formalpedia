-- Prove2me | Theorems.Thm_CorrelatedRounding_dilation_claim
-- name    : CorrelatedRounding.dilation_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:58.667325+00:00
-- url     : https://prove2.me/theorems/32e58ca7-eae3-48ab-a2f7-e1bb654f6976
-- title:
--   Proof of Lemma 1, p.10 — the clocks of an item are independent exponentials
-- statement:
--   Fix an item $i$ of an instance, and let $(E_k)_k$ be a draw of Algorithm 1. The random variables
--   $$\frac{y_k}{u_{ki}}E_k,\qquad k\text{ with } u_{ki}>0,$$
--   are independent, and each is exponentially distributed with rate $u_{ki}$, that is, with mean $1/u_{ki}$.
--
--   This is the step that turns one item's view of the algorithm into a race of independent exponentials, and the two later probability computations rest on it.
--
--   Differences from the source:
--   - encoding: the variables for all k = 1,…,K, with means 1/u_ki → the subtype of k with u_ki > 0; reason: at u_ki = 0 the page's mean is ∞ and the clock is the constant ∞, which has no exponential law
--   - encoding: "Index Z_i is determined by the smallest realization" → not restated here; it is the definition IsAlg1Output; reason: it is the algorithm's rule, not a separate claim
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Lemma 1, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **Dilation claim.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Lemma 1, p.10:
"Index Z_i is determined by the smallest realization among {(y_k/u_ki) E_k : k = 1,…,K}, which are
independent Exponential random variables with means {1/u_ki : k = 1,…,K}."

For a fixed item `i`, the variables `(y_k / u_ki) E_k` over the FCs with `u_ki > 0` are independent, and
each has law `Exp(rate u_ki)`, that is, mean `1/u_ki`.

**Formalization Note.** The family is indexed by the subtype `{k // 0 < u k i}`. At `u_ki = 0` the printed
mean is `∞` and the clock is the constant `⊤` by definition of `clock`, so these coordinates carry no law.
"Determined by the smallest realization" is the definition `IsAlg1Output`. -/
theorem dilation_claim {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (i : Fin q) :
    iIndepFun (fun (k : {k : Fin K // 0 < u k i}) (ω : Ω) => y u k / u k i * E k ω) μ ∧
      ∀ k : {k : Fin K // 0 < u k i},
        HasLaw (fun ω => y u k / u k i * E k ω) (expMeasure (u k i)) μ := by sorry

end CorrelatedRounding
