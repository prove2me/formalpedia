-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- name    : AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T09:06:31.089064+00:00
-- url     : https://prove2.me/theorems/74450e6a-3fcb-4b44-8fda-0fa53702ea5e
-- title:
--   Finite-cutoff original Gaussian residual second moment with near-zero jump correction
-- statement:
--   For every finite cutoff n and time t, the physical intrinsic residual has an integrable square whose expectation is t sigma squared plus the exact small-jump quadratic Lévy integral on (-1/(n+1),0). The endpoint is strict since the compensated source band includes -1/(n+1) and large marks include -1. This is an original same-space moment statement; no large-mark first absolute moment is assumed.
-- source:
--   Source-exact finite cutoff Gaussian variance identity. Completes missing baseline for 892afa4a after Proved original L2 residual error 41b16fe8. Use full-path law comparison 6c3e7ba6 and Borel marked jump statistic b50e56f2 with an independently constructed comparison model, or prove original joint Laplace source directly.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise22_original_gaussian_cutoff_exact_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
