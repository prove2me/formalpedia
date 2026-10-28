-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_increment_active_zero_real_laws_ws01b
-- name    : AvramDividend.Classical.bv_actual_increment_active_zero_real_laws_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T00:10:26.37832+00:00
-- url     : https://prove2.me/theorems/1cbd3145-f2a2-4c5c-8353-186282f5a1e3
-- title:
--   Exact actual-Lévy Bernoulli active/inactive cell probabilities in increment coordinates
-- statement:
--   For the actual bounded-variation finite-activity spectrally negative Lévy process, an increment X_t−X_s falls strictly below physical drift times elapsed time with probability 1−exp(−λ(t−s)), and it equals this drift amount with probability exp(−λ(t−s)), where λ is total negative-jump intensity. These are precisely the active and inactive grid-cell events used in the proved all-pattern joint product theorem. The result identifies the original increment-coordinate events, without introducing an auxiliary process.
-- source:
--   Convert the existing Proved drift-residual zero and positive increment probability identities to the equivalent increment half-line and singleton events. The only algebra is dt*drift−(X_t−X_s)=D_t−D_s and the nonnegative-real cast subtraction. Full Lean proof passed a private Prove2Me remote compiler probe on 28 October 2026.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_increment_active_zero_real_laws_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω | X.X t ω - X.X s ω <
      X.drift * (((t - s : ℝ≥0) : ℝ))} =
        1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) ∧
    P.real {ω : Ω | X.X t ω - X.X s ω =
      X.drift * (((t - s : ℝ≥0) : ℝ))} =
        Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
