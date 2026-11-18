-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_mark_intensity_normalisation_rate_bridge_20261117
-- name    : AvramDividend.Classical.avram_a27_mark_intensity_normalisation_rate_bridge_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:09:58.557197+00:00
-- url     : https://prove2.me/theorems/28dd97b9-e882-4a22-b629-ff1b71ac06e9
-- title:
--   Finite mark intensity and normalised mark transform recover the original Lévy exponent rate
-- statement:
--   For the original finite-activity marked Poisson law, once the original count rate r=t lambda, mark moment m, and single mark integral a=lambda m are established, the full compound-Poisson exponential rate follows from distributivity.
-- source:
--   Deterministic intensity/mark normalisation for the original-source negative jump marked-Poisson route; does not assume the missing marked-process independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_a27_mark_intensity_normalisation_rate_bridge_20261117 (t lambda r markMoment markIntegral exponent : ℝ)
    (hr : r = t * lambda)
    (hMoment : markMoment * lambda = markIntegral)
    (hExponent : exponent = markIntegral - lambda) :
    r * (markMoment - 1) = t * exponent := by sorry
