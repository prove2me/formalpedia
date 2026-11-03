-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_standing_positive_discount_unbounded_clock_cash_integrable
-- name    : AvramDividend.Classical.avram_wave6_08_original_standing_positive_discount_unbounded_clock_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:45:29.551816+00:00
-- url     : https://prove2.me/theorems/de6c04ba-a306-4611-b1e3-cec4b50e9388
-- title:
--   Original Standing Lévy unbounded random-clock complete dividend cash L1 for every q>0
-- statement:
--   Under the exact Standing and positive-discount hypotheses of corrected UBV verification, for every original admissible dividend D and every measurable potentially unbounded random clock τ, the original discounted complete Stieltjes cash.toReal is P-integrable. The source positive Laplace root φ with ψφ=q makes the previously proven θ-budget/L1 theorem applicable without any clock boundedness.
-- source:
--   Canonical source positive ψ root 1da68fa5, and to-be-Proved original θ unbounded random-clock cash L1 006d9506. Independent Chat08 direct cash L1 import for original arbitrary localising clocks in corrected 429; no Ito assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_unbounded_random_clock_stieltjes_cash_integrable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_original_standing_positive_discount_unbounded_clock_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by sorry
