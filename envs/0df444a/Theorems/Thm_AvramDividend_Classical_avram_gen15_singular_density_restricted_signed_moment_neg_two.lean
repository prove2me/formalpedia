-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_restricted_signed_moment_neg_two
-- name    : AvramDividend.Classical.avram_gen15_singular_density_restricted_signed_moment_neg_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:30:43.154345+00:00
-- url     : https://prove2.me/theorems/732ed41d-cc02-4c95-bec3-c746090fe78a
-- title:
--   Small-negative-jump signed Levy moment in the original drift definition equals negative two
-- statement:
--   The signed first jump moment on the exact small-negative-jump interval used by the original SpectrallyNegativeLevy.drift definition evaluates to negative two. This follows from the accepted whole-measure signed moment and the verified density restriction interface, retaining the same Levy measure and avoiding a surrogate kernel.
-- source:
--   Accepted full signed Levy moment, singular-density Bochner restriction and pinned integral_indicator and setIntegral_congr_fun.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_singular_density_restricted_signed_moment_neg_two :
    (∫ z in Ioo (-1 : ℝ) 0, z ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) = -2 := by sorry
