-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_large_only_residual_eq_gaussian
-- name    : AvramDividend.Classical.avram_b27_original_intrinsic_large_only_residual_eq_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:42:08.566395+00:00
-- url     : https://prove2.me/theorems/ae82078a-4cac-4fb2-b429-cdb65dab5faa
-- title:
--   The original intrinsic residual exactly equals its Gaussian path for a large-only negative mark Lévy source
-- statement:
--   For the exact original Lévy source X on a physical sample path with c=0, X_t=B_t-2N_t, the intrinsic signed large-jump integral equal to -2N_t, and every nonzero jump mark at most -1 with no small-negative-mark measure mass, the original cut-off truncated residual X_t-tc-Jsmall_k(t)-Jlarge(t) is exactly B_t for every cutoff k and time t. Imports the original-source no-small-band lemma as its only substantive stochastic dependency. No replacement martingale, copied data or post-ruin stopping clock.
-- source:
--   B25 two-channel physical-source large-jump compensation audit, 15 November 2026; exact published original intrinsic residual and signed large-jump sum definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b27_original_intrinsic_large_only_residual_eq_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (B N : ℝ≥0 → ℝ)
    (hc : X.c = 0)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (hPath : ∀ t : ℝ≥0, X.X t ω = B t - 2 * N t)
    (hLargeSum : ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -2 * N t)
    (hJumps : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1)) :
    ∀ (k : ℕ) (t : ℝ≥0),
      avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω = B t := by sorry
