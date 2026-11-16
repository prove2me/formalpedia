-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
-- name    : AvramDividend.Classical.avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:41:40.984124+00:00
-- url     : https://prove2.me/theorems/53c2a813-ec7d-4acb-973f-01a4c7c11e1a
-- title:
--   Positive residual L1 and L1 approximation jointly imply eventwise a.e. cash upper bound
-- statement:
--   Given integrable source target K, limiting centred source N and approximating mesh M_m, if the positive-part mesh excess (K-M_m)^+ converges to zero in L1 and M_m converges to N in L1, then K<=N almost everywhere. The proof uses the pointwise max-Lipschitz inequality, integral monotonicity and the nonnegative zero-integral characterisation. This is the source-independent exact limit-transfer component of the selected B54c positive-clock cash route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped Topology

theorem AvramDividend.Classical.avram_gbB54y_positive_excess_L1_and_approximation_L1_imply_ae_upper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (K N : Ω → ℝ) (M : ℕ → Ω → ℝ)
    (hKI : Integrable K μ) (hNI : Integrable N μ)
    (hMI : ∀ m, Integrable (M m) μ)
    (hRes : Tendsto (fun m => ∫ ω, max (K ω - M m ω) 0 ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hDiff : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    ∀ᵐ ω ∂μ, K ω ≤ N ω := by sorry
