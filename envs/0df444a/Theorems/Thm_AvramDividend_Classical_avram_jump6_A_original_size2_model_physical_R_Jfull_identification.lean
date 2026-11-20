-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_size2_model_physical_R_Jfull_identification
-- name    : AvramDividend.Classical.avram_jump6_A_original_size2_model_physical_R_Jfull_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:26:47.656175+00:00
-- url     : https://prove2.me/theorems/d0f2ccc6-2697-46df-9dc5-48bd9a84630c
-- title:
--   Identify the original intrinsic Gaussian and unit-fullmark channels in the size-two Brownian-Poisson physical model
-- statement:
--   On an actual large-negative-jump-only original spectrally negative Lévy sample path X=B−2N, with physical large mark sum −2N, intrinsic limiting Gaussian source and zero smallmark source, identify the unique Gaussian source R exactly with B, and the original fixed unit-coefficient Jfull source exactly with −2N+2t under the actual one-step expectation −2. This uses the Proved all-cutoff intrinsic residual identity ae82078a and no synthetic noise witnesses. These physical identifications complete the nontrivial source algebra for the proposed ruin-jump counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_size2_model_physical_R_Jfull_identification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B N : ℝ≥0 → ℝ)
    (R Jsmall Jfull : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * N t)
    (hLarge : ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t)
    (hJumps : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (hR : ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJzero : ∀ t : ℝ≥0, Jsmall t ω = 0)
    (hFull : ∀ t : ℝ≥0, Jfull t ω = Jsmall t ω +
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - ∫ η, X.X 1 η ∂P))
    (hMean : (∫ η, X.X 1 η ∂P) = (-2 : ℝ)) :
    (∀ t : ℝ≥0, R t ω = B t) ∧
    (∀ t : ℝ≥0, Jfull t ω = -2 * N t + 2 * (t : ℝ)) := by sorry
