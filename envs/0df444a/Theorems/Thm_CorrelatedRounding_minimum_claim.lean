-- Prove2me | Theorems.Thm_CorrelatedRounding_minimum_claim
-- name    : CorrelatedRounding.minimum_claim
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:57.370083+00:00
-- url     : https://prove2.me/theorems/0f24998e-6baf-49ab-b5b5-69c1cdab6bd9
-- title:
--   Proof of Lemma 2, pp.10–11 — the minimum clock of an item is $\mathrm{Exp}(1)$
-- statement:
--   Fix an item $i$ and a draw of Algorithm 1. The minimum
--   $$\min_{k}\frac{y_k}{u_{ki}}E_k$$
--   is exponentially distributed with mean $1/(u_{1i}+\dots+u_{Ki})=1$, and consequently, for $t\ge0$,
--   $$\Pr\Big[\min_k \frac{y_k}{u_{ki}}E_k\ge t\Big]=e^{-t}.$$
--   This is the bound on one item still waiting at time $t$, which Lemma 2 sums over the items.
--
--   Differences from the source:
--   - encoding: the minimum over all k = 1,…,K → the law is stated for the real minimum over k with u_ki > 0; the tail is stated with all EReal clocks; reason: the other clocks are ∞; the real minimum has an exponential law
--   - reading: Pr[min ≥ t] = e^{−t}, with t implicit → the clause for t ≥ 0; reason: Lemma 2 fixes t ≥ 0; at t < 0 the probability is 1
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Lemma 2, pp.10–11

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **Minimum claim.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Lemma 2, pp.10–11:
"Therefore, min_k (y_k/u_ki) E_k is Exponentially distributed with mean 1/(u_1i + ⋯ + u_Ki) = 1.
Consequently, Pr[min_k (y_k/u_ki) E_k ≥ t] = e^{−t}".

For a fixed item `i`, the minimum of the finite clocks has law `Exp(rate 1)`, and for `t ≥ 0` the event that
all clocks are at least `t` has probability `e^{−t}`.

**Formalization Note.** The law is stated for the real minimum over the FCs with `u_ki > 0`, the other clocks
being `⊤`. That index type is finite and, on an instance, nonempty, so the `⨅` is an attained minimum. The
tail is stated with the `EReal` clocks over all `k`. The paper uses it for `t ≥ 0`; for `t < 0` the
probability is `1`, not `e^{−t}`. -/
theorem minimum_claim {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (i : Fin q) :
    HasLaw (fun ω => ⨅ k : {k : Fin K // 0 < u k i}, y u k / u k i * E k ω) (expMeasure 1) μ ∧
      ∀ t : ℝ, 0 ≤ t →
        μ {ω | ∀ k, (t : EReal) ≤ clock u (fun k' => E k' ω) k i} =
          ENNReal.ofReal (Real.exp (-t)) := by sorry

end CorrelatedRounding
