-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_preruin_preterminal_drift_strip
-- name    : AvramDividend.Classical.avram_p3_bv_preruin_preterminal_drift_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:22:52.28021+00:00
-- url     : https://prove2.me/theorems/11a76c2c-3404-432e-ba85-9b012a99a9dc
-- title:
--   Actual BV strict-survival pre-rightpayment reserve lies in physical drift strip
-- statement:
--   For the genuine bounded-variation spectrally negative source and original nondecreasing dividend path, at any deterministic horizon strictly preceding ruin, the book reserve before that time's right dividend lies in the deterministic strip [0, x+T d] almost surely. The source zero-origin property is explicit and can be discharged from the original spectral process record. Does not assert a jump compensator or the stopped HJB budget.
-- source:
--   Original pathwise BV drift residual monotonicity, nonnegative dividend path, and pre-ruin reserve nonnegativity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_preruin_preterminal_drift_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hXzero : ∀ ω, X.X 0 ω = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (S : ℝ≥0) :
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ riskProcess X x D S ω ∧
      riskProcess X x D S ω ≤ x + (S : ℝ) * X.drift := by sorry
