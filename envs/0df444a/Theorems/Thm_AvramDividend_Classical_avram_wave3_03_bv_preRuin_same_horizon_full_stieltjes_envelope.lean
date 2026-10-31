-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_preRuin_same_horizon_full_stieltjes_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_preRuin_same_horizon_full_stieltjes_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:43:13.526355+00:00
-- url     : https://prove2.me/theorems/a8ad19f5-1413-4f60-b443-7f6b4a8afc92
-- title:
--   Same-time BV stopped Stieltjes drift envelope on the genuine strict pre-ruin event
-- statement:
--   On every genuine strictly pre-ruin finite horizon T, the complete stopped dividendMeasure payout through T is almost surely bounded by ENNReal.ofReal(x+T*X.drift). This includes singular/absolutely continuous dividend mass, time zero, and the right payment at T. Combines the source original BV full-mass drift envelope and the original ruin-time right-neighbourhood solvency result without assuming full HJB compensation.
-- source:
--   Accepted same-horizon full Stieltjes drift envelope c335db18; source preRuin eventually right solvent e8ccd8aa (pending proof at drafting).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_preRuin_eventually_right_solvent

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_preRuin_same_horizon_full_stieltjes_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
