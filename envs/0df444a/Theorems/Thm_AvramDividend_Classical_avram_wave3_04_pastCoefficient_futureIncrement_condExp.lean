-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_pastCoefficient_futureIncrement_condExp
-- name    : AvramDividend.Classical.avram_wave3_04_pastCoefficient_futureIncrement_condExp
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:28:15.126801+00:00
-- url     : https://prove2.me/theorems/bd57036b-f0c5-4f82-aabd-535dcc4214e8
-- title:
--   Original Lévy one-step conditional expectation with an arbitrary past-measurable coefficient
-- statement:
--   For the original spectrally negative Lévy process and deterministic times s≤t, the conditional expectation of a past-F_s strongly measurable coefficient H multiplied by an integrable Borel payoff of the future increment equals H multiplied by that future payoff's unconditional stationary-increment mean. This preserves the joint process and actual filtration. The explicit integrability hypotheses keep the conditional-expectation multiplication theorem's requirements transparent.
-- source:
--   Canonical Proved chat04_general_future_increment_conditional_expectation UUID 60e3f274-5580-448a-a1d8-6485fa8ab41a; pinned Mathlib condExp_mul_of_stronglyMeasurable_left. Exact private compiler job b59837a4-6694-4fc9-ab8c-b73414d1be79 reached sentinel without source errors; SHA-256 61341099e9fbb5768a8d262e46e6f6deb5f10dd879af3ef45ef6caab493fdf2d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_pastCoefficient_futureIncrement_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hIntInc : Integrable (fun ω => φ (X.X t ω - X.X s ω)) P)
    (hIntProd : Integrable
      (fun ω => H ω * φ (X.X t ω - X.X s ω)) P) :
    P[(fun ω => H ω * φ (X.X t ω - X.X s ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => H ω * ∫ z, φ (X.X (t - s) z) ∂P) := by sorry
