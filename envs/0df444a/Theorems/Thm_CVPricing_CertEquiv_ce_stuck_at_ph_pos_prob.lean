-- Prove2me | Theorems.Thm_CVPricing_CertEquiv_ce_stuck_at_ph_pos_prob
-- name    : CVPricing.CertEquiv.ce_stuck_at_ph_pos_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:35:45.046541+00:00
-- url     : https://prove2.me/theorems/2fe1f1e1-7985-4eb7-9a2d-c2942a878e67
-- title:
--   p. 775 — with positive probability, certainty equivalent pricing charges $p_t = p_h$ for all $t \ge 3$
-- statement:
--   Consider the model of `CVPricing.CertEquiv.Model` with two different initial prices $p_1 \ne p_2$ in $[p_l, p_h]$, and independent $N(0, \sigma^2)$ demand noise $e_1, e_2, \dots$ on a probability space $(\Omega, P)$, so that $d_t = a_0^{(0)} + a_1^{(0)}p_t + e_t$. Let $(p_t)$ be the certainty equivalent price path. Then
--
--   $$P\big(p_t = p_h \text{ for all } t \ge 3\big) > 0 .$$
--
--   This is the claim that the proof of Proposition 1 actually establishes; since $p_{\mathrm{opt}} < p_h$, it implies Proposition 1.
--
--   **Formalization Note** The paper's $e_i$ is `ε (i - 1)` (the referenced noise is indexed from $0$). Prices are evaluated pathwise: for each outcome $\omega$, the price path is `cePrice` applied to the noise path $i \mapsto e_i(\omega)$. Both orders of the initial prices are covered.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 775 (PDF 7), the paragraph after Proposition 1: 'The idea of the proof is to show by induction that with positive probability, p_t = p_h for all t ≥ 3.'

import Mathlib
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_CVPricing_CertEquiv_CEPrice

namespace CVPricing.CertEquiv

open MeasureTheory ProbabilityTheory

theorem ce_stuck_at_ph_pos_prob (M : Model) {p₁ p₂ : ℝ} (hp₁ : p₁ ∈ Set.Icc M.pl M.ph)
    (hp₂ : p₂ ∈ Set.Icc M.pl M.ph) (hne : p₁ ≠ p₂)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ε : ℕ → Ω → ℝ} (hε : RobustBooking.Shared.GaussianNoise M.σ P ε) :
    0 < P {ω | ∀ t : ℕ, 3 ≤ t → cePrice M p₁ p₂ (fun i => ε (i - 1) ω) t = M.ph} := by sorry

end CVPricing.CertEquiv
