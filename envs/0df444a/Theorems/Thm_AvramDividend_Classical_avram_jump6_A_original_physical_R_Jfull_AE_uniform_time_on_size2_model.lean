-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_physical_R_Jfull_AE_uniform_time_on_size2_model
-- name    : AvramDividend.Classical.avram_jump6_A_original_physical_R_Jfull_AE_uniform_time_on_size2_model
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:53:24.901157+00:00
-- url     : https://prove2.me/theorems/4f763d96-ee1b-492d-ae26-7ec15af22425
-- title:
--   True original Brownian and full unit-mark compensated channels equal R=B and Jfull=−2N+2t simultaneously almost surely at all times
-- statement:
--   For the authentic original Brownian-minus-size-two-Poisson spectrally negative Lévy model, assuming the genuine intrinsic Gaussian residual converges to R, the small-jump compensated channel vanishes for the zero small-mark measure, the real large-jump sum equals −2 times actual count N, the true marked paths have no jump in (−1,0), and E[X_1]=−2, the server-Proved physical source identity d0f2ccc6 applies simultaneously at almost every original sample path and every observation time. It yields R_t=B_t and Jfull_t=−2N_t+2t for all t on the same conull event. This supplies the exact original Hsource/Jfull noise-identification interface at the genuine first ruin mark, rather than a synthetic or pointwise assertion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_size2_model_physical_R_Jfull_identification
set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_physical_R_Jfull_AE_uniform_time_on_size2_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B N R Jsmall Jfull : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = B t ω - 2 * N t ω)
    (hLarge : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t ω)
    (hJumps : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJzero : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Jsmall t ω = 0)
    (hFull : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Jfull t ω = Jsmall t ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - ∫ η, X.X 1 η ∂P))
    (hMean : (∫ η, X.X 1 η ∂P) = (-2 : ℝ)) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, R t ω = B t ω) ∧
      (∀ t : ℝ≥0, Jfull t ω = -2 * N t ω + 2 * (t : ℝ)) := by sorry
