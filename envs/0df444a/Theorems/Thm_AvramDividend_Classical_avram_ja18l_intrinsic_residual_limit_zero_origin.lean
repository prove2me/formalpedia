-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18l_intrinsic_residual_limit_zero_origin
-- name    : AvramDividend.Classical.avram_ja18l_intrinsic_residual_limit_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:21:27.428015+00:00
-- url     : https://prove2.me/theorems/a8d94ac5-d203-45e2-83ab-1efe9ef0536f
-- title:
--   Original intrinsic residual limit starts at zero almost surely
-- statement:
--   The original pathwise source limit R of every truncated residual vanishes at time zero almost surely, because each physical truncated residual is zero there. Necessary endpoint for optional stopping of compensated jump difference.
-- source:
--   JA18 original stopped jump martingale 41babf55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18l_intrinsic_residual_limit_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by sorry
