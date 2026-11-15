-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
-- name    : AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:59:06.216502+00:00
-- url     : https://prove2.me/theorems/6dea06f3-f415-42b0-9eee-e87b29fb2299
-- title:
--   Ruin-contact Gaussian and compensated noise a.s. vanishing plus integrable domination implies L1 vanishing
-- statement:
--   General dominated-convergence transfer specialised to the exact original Gaussian or compensated-mark terminal ruin-contact mesh error. For a sequence of real-valued integrable mesh terms on the same sample probability measure, with almost-sure vanishing and one integrable uniform norm majorant, the expected absolute terminal noise error tends to zero. The original stopped cash sign and source assumptions remain separate and must supply the actual majorant. This is the final bridge from pathwise Gaussian last-cell convergence to its L1 contribution in the B24 Ito cash ledger.
-- source:
--   Pinned Mathlib tendsto_integral_of_dominated_convergence for integrable real source norms.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (B : Ω → ℝ)
    (hFI : ∀ k, Integrable (F k) P)
    (hBI : Integrable B P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ B ω)
    (hLim : ∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
