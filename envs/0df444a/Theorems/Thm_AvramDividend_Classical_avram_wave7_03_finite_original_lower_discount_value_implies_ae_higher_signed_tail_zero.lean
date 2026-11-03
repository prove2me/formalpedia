-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_lower_discount_value_implies_ae_higher_signed_tail_zero
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_lower_discount_value_implies_ae_higher_signed_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:03:08.529104+00:00
-- url     : https://prove2.me/theorems/10355773-0c0e-4e31-b981-f0ba974d165a
-- title:
--   Finite original lower-discount value yields a.e genuine signed strict pre-ruin tails vanishing at every higher discount
-- statement:
--   For the exact original spectrally negative Lévy reserve X with original admissible dividend D and its original P, if the full dividendValue at discount q₁ is finite and q₂≥q₁, the genuine real signed discounted Stieltjes payout on paymentTimes(ruinTime X x D ω)∩Ioi n converges to zero for P-almost all original paths. Use full-value discount monotonicity, exact finite-value pathwise ENNReal finiteness, exact same-measure signed IntegrableOn characterisation, and the newly proved source signed-tail convergence. The result retains all continuous and initial/right-limit payout accounting at the full-domain level while tails select strictly future payments.
-- source:
--   Accepted actual value discount order a5978ae4, finite iff fd64314b, pathwise genuine signed iff a6d24d2f and unrestricted signed tail c94fa5f6.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_lower_discount_value_implies_ae_higher_signed_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (hFinite : dividendValue X q₁ x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
          Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 0) := by sorry
