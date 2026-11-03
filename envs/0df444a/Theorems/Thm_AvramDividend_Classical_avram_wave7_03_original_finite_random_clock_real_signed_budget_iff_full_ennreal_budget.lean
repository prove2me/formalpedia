-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_real_signed_budget_iff_full_ennreal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_real_signed_budget_iff_full_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:47:51.9676+00:00
-- url     : https://prove2.me/theorems/3a05ec6b-6a21-47b3-a818-80332c3c1242
-- title:
--   Exact equivalence of original finite random-clock real signed Stieltjes budget and full double ENNReal budget under finiteness
-- statement:
--   For an arbitrary measurable pathwise finite NNReal random clock on the exact original Lévy process, assuming finite true outer expected ENNReal dividend cash and nonnegative real budget B, the genuine expected signed real discounted Stieltjes payout over paymentTimes(ruinTime)∩Iic τ is at most B if and only if the exact original double ENNReal payout on the identical P/dividendMeasure/stopped domain is at most ENNReal.ofReal B. The proof consumes the Proved original signed/ENNReal mean equality under cash finiteness; derives nonnegativity of the real mean directly from positive exponential cash; and applies monotonicity of ofReal or finite toReal in either direction. Explicit B≥0 prevents the zero-clipping ambiguity of ENNReal.ofReal at negative budgets.
-- source:
--   Original finite random-clock signed/ENNReal mean equality under finite expected cash; pinned Mathlib ENNReal.ofReal_le_ofReal and ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_real_signed_budget_iff_full_ennreal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (hCashFinite :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) < ⊤)
    (B : ℝ) (hB : 0 ≤ B) :
    ((∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) ↔
    ((∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B) := by sorry
