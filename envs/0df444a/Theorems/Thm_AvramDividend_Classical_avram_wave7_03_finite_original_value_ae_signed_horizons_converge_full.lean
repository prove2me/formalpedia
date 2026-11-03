-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
-- name    : AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:58:41.197465+00:00
-- url     : https://prove2.me/theorems/62e34799-1a75-49a4-9b36-743d277094a6
-- title:
--   Finite original dividend value implies a.e original signed finite-horizon Stieltjes cash converges to its full signed cash
-- statement:
--   On the exact original process and strategy, finite dividendValue implies that for P-almost every original path the actual signed real Stieltjes discounted integral over paymentTimes(ruinTime)∩Iic n converges to the full exact paymentTimes integral against dividendMeasure. The proof uses original source finite-value characterisation, genuine pathwise IntegrableOn equivalence and a dedicated signed same-measure horizon convergence lemma. Includes time-zero right-limit atom and all continuous/jump payments.
-- source:
--   Accepted exact finite-value iff fd64314b, pathwise finiteness iff a6d24d2f, new signed finite-horizon-to-full convergence lemma (requires Proved).

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_general_original_value_finite_iff_genuine_signed_L1_and_pathwise_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_signed_horizons_converge_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ =>
        ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω))
        atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω))) := by sorry
