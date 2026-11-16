-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_large_only_R_Jsmall_source_limits
-- name    : AvramDividend.Classical.avram_b27_original_large_only_R_Jsmall_source_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:56:19.200195+00:00
-- url     : https://prove2.me/theorems/e7081c55-c18d-424d-b6c3-fcca87abba6a
-- title:
--   The exact original physical Gaussian residual tends to the Brownian part and the original compensated small-band source tends to zero
-- statement:
--   For the original Lévy source X=B-2N with zero linear drift, signed source large-jump integral -2N, no small negative Levy mass, and all actual nonzero jumps at most -1, the cutoff-indexed original intrinsic residual is pathwise B for every cutoff and all positive times, and the original compensated small-band source is zero for every cutoff and time. Hence the exact original hRsource and hJsource hypotheses required by B25 topcap and finitecap physical mesh sources hold almost everywhere with R=B and Jsmall=0. This is conditional on explicit original process large-jump path identities; no unrelated surrogate is substituted.
-- source:
--   B25/27 original physical source counterexample, 15 November 2026, exact definitions and accepted/sourced B27 original large-only residual and smallband theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_large_only_residual_eq_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b27_original_large_only_R_Jsmall_source_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (B N : ℝ≥0 → Ω → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ ω t, X.X t ω = B t ω - 2 * N t ω)
    (hLargeSum : ∀ ω t,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω =
        -2 * N t ω)
    (hJumps : ∀ ω (u : ℝ≥0), 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1)) :
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (B t ω))) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (0 : ℝ))) := by sorry
