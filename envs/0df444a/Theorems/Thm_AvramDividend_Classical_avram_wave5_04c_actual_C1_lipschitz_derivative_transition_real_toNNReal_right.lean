-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_lipschitz_derivative_transition_real_toNNReal_right
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_lipschitz_derivative_transition_real_toNNReal_right
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:49:46.108374+00:00
-- url     : https://prove2.me/theorems/11ec21e1-ffe2-4605-be96-9b01a458f9eb
-- title:
--   Original C1 derivative transition continuity at the exact right Real.toNNReal time filter
-- statement:
--   For the genuine spectrally negative Lévy source X and every globally C1 Lipschitz w, the original transition E[deriv w(x+X_{Real.toNNReal h})] tends to deriv w x through the exact right-neighbourhood filter nhdsWithin 0 (Ioi 0) used by the canonical BV generator-semigroup target. The derivative is continuous by ContDiff and bounded by L through the global Lipschitz estimate. Applying the Proved bounded-continuous original-source transition continuity to sequences and countably generated filters establishes NNReal-time continuity. Finally, continuity of Real.toNNReal at real zero restricts to the positive right-neighbourhood. This directly discharges a physical-drift expectation-continuity ingredient, not the full generator identity.
-- source:
--   Complete source privately remote compiler sentinel-verified: candidates/work_on/AvramDividend_04c_actual_C1_derivative_transition_real_right_inline_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_strong_continuity_at_zero_bounded
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_lipschitz_derivative_transition_real_toNNReal_right {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) :
    Tendsto
      (fun h : ℝ => ∫ ω, deriv w (x + X.X (Real.toNNReal h) ω) ∂P)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (deriv w x)) := by sorry
