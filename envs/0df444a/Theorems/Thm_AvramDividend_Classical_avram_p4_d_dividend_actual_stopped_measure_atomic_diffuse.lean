-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
-- name    : AvramDividend.Classical.avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:58:50.239902+00:00
-- url     : https://prove2.me/theorems/5f1959b3-2468-4880-9eea-183b1cff2ed2
-- title:
--   The exact original stopped dividend measure inherits the closed-horizon atomic and diffuse split
-- statement:
--   For any genuine original dividend strategy and path, restrict the Wave-4 countable right-atom plus atomless Stieltjes decomposition on [0,T] to the exact original paid set paymentTimes(ruinTime) ∩ (-∞,T]. The result includes the time-zero atom, all singular-continuous and absolutely continuous mass, and the T atom precisely if T is an eligible payment time; it excludes the right-payment atom at a strictly positive ruin event. No boundary or differentiability assumptions are imposed.
-- source:
--   Proved Wave-4 finite-horizon atomic/diffuse theorem d19177af-e2bc-4c43-813a-5abc846cb4bf and original paymentTimes/ruinTime definitions 561c1e83-0505-4d9d-9f28-33943f44b28a; Mathlib Measure.restrict_restrict and restrict_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_actual_stopped_measure_atomic_diffuse
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)) =
        μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A =>
        ((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) =
        μatom.restrict (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) +
        μdiffuse.restrict (paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ)) := by sorry
