-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_closed_horizon_discounted_atomic_cash_series_bounded
-- name    : AvramDividend.Classical.avram_wave6_05_actual_closed_horizon_discounted_atomic_cash_series_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:42:46.99432+00:00
-- url     : https://prove2.me/theorems/cef61819-f9b6-4f0d-98e0-c70abdf852b7
-- title:
--   Exhaustive original discounted countable right-atom dividend cash series bounded by the cumulative actual payment
-- statement:
--   For every actual adapted nondecreasing original dividend strategy and every nonnegative discount and finite closed horizon, its original dividendMeasure has a countable exhaustive right-atomic support A and actual atomless μdiffuse, with full rightLimit singleton identities and exact full weighted cash decomposition. The discounted sum of ALL original right-payment atomic cash through T is bounded above by ENNReal.ofReal(rightLimit D T ω), with no finite-jump, smooth-control or reserve-interior assumption. The unchanged diffuse term includes continuous and singular-continuous payment variation, and the right atoms include time zero and the horizon endpoint even when Lévy source jumps coincide. This supplies a concrete finite-budget upper bound for chronological atomic dividends in the genuine controlled Ito–Meyer accounting.
-- source:
--   Instantiate the canonically accepted exact full original Stieltjes all-atoms plus atomless identity with the nonnegative discount weight. Its countable atomic support is exhaustive by the accepted support theorem. Since an ENNReal lower integral against the actual diffuse measure is nonnegative, the atomic countable sum is no greater than the complete original dividendMeasure discounted integral. Apply the canonically Proved closed-horizon Stieltjes mass bound for q≥0 to dominate that complete integral by the actual cumulative right-limit dividend. No finite-jump representation or dividend-control regularity is imposed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_closed_horizon_discounted_atomic_cash_series_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) ≤
        ENNReal.ofReal (rightLimit D T ω)) := by sorry
