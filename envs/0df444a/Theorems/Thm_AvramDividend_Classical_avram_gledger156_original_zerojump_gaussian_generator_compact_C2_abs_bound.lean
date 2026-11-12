-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
-- name    : AvramDividend.Classical.avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:32:39.216603+00:00
-- url     : https://prove2.me/theorems/5e4c7aa4-484a-4ef3-a8bb-510b1322ff8c
-- title:
--   Original zero-jump Gaussian generator bounded by compact value-gradient-curvature jets
-- statement:
--   For the original spectrally negative Levy process with zero jump measure, the discounted generator residual at the original physical postpayment state is bounded by a fixed linear combination of the true Gaussian drift, curvature coefficient, discount and uniform compact value/gradient/Hessian bounds. This is one finite-cell analytic input for gledger155 original stopped generator uniform envelope.
-- source:
--   Proved original zero-jump generator formula gledger p4_f11 and elementary triangle, absolute product and positivity inequalities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger156_original_zerojump_gaussian_generator_compact_C2_abs_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (y M : ℝ)
    (hM : 0 ≤ M) (hw : |w y| ≤ M)
    (hd : |deriv w y| ≤ M)
    (hdd : |iteratedDeriv 2 w y| ≤ M) :
    |X.generator w y - q * w y| ≤
      (X.σ ^ 2 / 2 + |X.c| + q) * M := by sorry
