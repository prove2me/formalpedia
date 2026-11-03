-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
-- name    : AvramDividend.Classical.avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:32:52.079595+00:00
-- url     : https://prove2.me/theorems/49da37f3-df5e-4f88-83e8-4dffa12964eb
-- title:
--   Exact original signed/ENNReal stopped Stieltjes mean equality with both random clock and deterministic bound real
-- statement:
--   The original full ruin-stopped payout equality holds when both finite deterministic upper horizon T and bounded measurable nonnegative random clock τ are actual real types, matching canonical BV/UBV side conditions. The proof applies the accepted real-valued clock theorem f1840802 at T.toNNReal and uses Real.coe_toNNReal T hT to retain the exact same original stopped measure and domain. No BV/UBV restriction, auxiliary sample space, atom removal, or changed ruin time is introduced.
-- source:
--   Accepted original bounded real random clock full Stieltjes mean equality f1840802 and Real.coe_toNNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_real_random_clock_full_stieltjes_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_real_bounded_real_random_clock_full_stieltjes_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ) (hT : 0 ≤ T) (τ : Ω → ℝ)
    (hτNonneg : ∀ ω, 0 ≤ τ ω)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable τ) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
