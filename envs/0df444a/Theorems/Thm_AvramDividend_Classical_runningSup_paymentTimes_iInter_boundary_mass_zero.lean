-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_boundary_mass_zero
-- name    : AvramDividend.Classical.runningSup_paymentTimes_iInter_boundary_mass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:47:07.708655+00:00
-- url     : https://prove2.me/theorems/78247be5-95be-4511-8291-b38da679b959
-- title:
--   The endpoint difference of shrinking dividend payment windows has zero Stieltjes mass
-- statement:
--   For any countable family of stopping horizons and every Lévy sample path, the portion of their common strict dividend-payment window omitted by the window at the infimum has zero running-supremum Stieltjes measure. The set difference lies in the singleton of the limiting terminal time, and the actual dividend measure is atomless at nonnegative times. This is the endpoint-nullity argument needed for monotone zero-barrier Stieltjes reward limits.
-- source:
--   Proved runningSup_dividendMeasure_no_nonnegative_atoms and newly submitted paymentTimes_iInter_diff_iInf_subset_terminal. Supports zero-cap reflection valuation.

import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_paymentTimes_iInter_diff_iInf_subset_terminal
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_nonnegative_atoms

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_paymentTimes_iInter_boundary_mass_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) :
    (dividendMeasure (runningSup X) ω)
      ((⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n)) = 0 := by sorry
