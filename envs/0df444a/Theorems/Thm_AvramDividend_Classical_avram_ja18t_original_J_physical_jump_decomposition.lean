-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18t_original_J_physical_jump_decomposition
-- name    : AvramDividend.Classical.avram_ja18t_original_J_physical_jump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:47:44.825055+00:00
-- url     : https://prove2.me/theorems/ce29c6e1-d6cd-41ac-9fe8-1f3060820251
-- title:
--   Original jump martingale equals small compensated jump limit plus actual large-jump sum and drift
-- statement:
--   The original truncated Gaussian residual is definitionally X_t - t c - smallband_k(t) - actual_largejump(t). Both R and Jsmall are simultaneous almost-sure pointwise limits, so uniqueness gives the stated exact pathwise decomposition for all t. This links the stopped J martingale to already proved small-band envelopes and large-jump integrability.
-- source:
--   J-A18 finite activity original stopped jump 41babf55, JA18P

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18t_original_J_physical_jump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω - (t : ℝ) * (∫ η, X.X 1 η ∂P) - R t ω =
        Jsmall t ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        (t : ℝ) * (X.c - (∫ η, X.X 1 η ∂P)) := by sorry
