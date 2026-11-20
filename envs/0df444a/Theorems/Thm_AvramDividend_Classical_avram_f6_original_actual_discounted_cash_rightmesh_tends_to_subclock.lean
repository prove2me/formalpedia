-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
-- name    : AvramDividend.Classical.avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:26:16.083637+00:00
-- url     : https://prove2.me/theorems/ed1f30f9-9b4f-467f-91cd-db8b9ab490bc
-- title:
--   Original true dividendMeasure inclusive cash rightmesh converges at every subclock
-- statement:
--   For each physical original Lévy and admissible dividend path, discounted inclusive Iic dividendMeasure cash toReal at ρm=min(τ,σ+1/(m+1)) converges to cash at σ≤τ. Uses genuine paymentTimes, exact ruinTime and finite true Stieltjes cash on bounded horizons, preserving contact atoms. Needed for F6 almost-everywhere ruin-contact reward convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_weighted_inclusive_cash_rightclock_limit
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_finite_horizon_real_ennreal_eq
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_actual_discounted_cash_rightmesh_tends_to_subclock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω)
    (σ τ : ℝ≥0) (hστ : σ ≤ τ) :
    Tendsto (fun m : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iic ((min τ (σ + (1 : ℝ≥0) /
            ((m : ℝ≥0) + 1)) : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal) atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal)) := by sorry
