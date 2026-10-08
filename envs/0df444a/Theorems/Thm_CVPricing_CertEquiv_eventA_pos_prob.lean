-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_eventA_pos_prob
-- name    : CVPricing.CertEquiv.eventA_pos_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:36:18.618914+00:00
-- url     : https://prove2.me/theorems/d5e9e882-f60f-4562-ad3c-c7e38fd28d43
-- title:
--   Proof of Proposition 1, p. 780 — for $\delta$ sufficiently large, $P(A) > 0$
-- statement:
--   Consider the model of `CVPricing.CertEquiv.Model` and initial prices $p_l \le p_1 < p_2 \le p_h$. Let $A_\delta$ be the event of `CVPricing.CertEquiv.EventA`. There is $\delta_0 > 0$, depending only on the model and the initial prices, such that for every $\delta \ge \delta_0$ and every probability space $(\Omega, P)$ carrying independent $N(0, \sigma^2)$ noise $e_1, e_2, \dots$,
--
--   $$P(A_\delta) > 0 .$$
--
--   This is where the probability in Proposition 1 comes from: the deterministic induction shows that the certainty equivalent price is stuck at $p_h$ on $A_\delta$, and this theorem shows the event is not negligible.
--
--   **Formalization Note** The proof assumes $p_1 < p_2$ without loss of generality; the statement is made under that ordering. The paper's $e_i$ is `ε (i - 1)` (the referenced noise is indexed from $0$). The event uses the corrected definition of $A$ (see `EventA`). As written, the proof chooses $\delta$ after a set $B$ of solutions of (12) that itself depends on $\delta$; the statement is unaffected (see the mission description).
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 780 (PDF 12), Appendix, proof of Proposition 1, 'We first show that for sufficiently large δ, the event A occurs with strictly positive probability' … 'This proves that for δ sufficiently large, the event A occurs with probability P(A) > 0.'

import Mathlib
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_CVPricing_CertEquiv_EventA

namespace CVPricing.CertEquiv

open MeasureTheory ProbabilityTheory

theorem eventA_pos_prob (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (h12 : p₁ < p₂) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ₀ ≤ δ →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ), RobustBooking.Shared.GaussianNoise M.σ P ε →
        0 < P {ω | EventA M p₁ p₂ δ (fun i => ε (i - 1) ω)} := by sorry

end CVPricing.CertEquiv
