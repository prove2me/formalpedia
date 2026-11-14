-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt
-- name    : AvramDividend.Classical.avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:21:18.31488+00:00
-- url     : https://prove2.me/theorems/ba71a622-a613-4e38-ba09-d63d754817b2
-- title:
--   Positive Gaussian spatial Chernoff tilt optimised to quadratic exponential mesh large-tail decay
-- statement:
--   For a positive Gaussian physical mesh width d, source exponential weight theta and threshold δ at least theta d, the nonnegative optimal Chernoff tilt δ/d−theta gives the Gaussian rare-tail exponent thetaδ−δ squared divided by twice d.
-- source:
--   Source exact ga_a61 original Gaussian upper spatial rare excursion, positive-only b0d9951c Taylor mesh.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a62_positive_gaussian_chernoff_optimal_mesh_tilt (d θ δ : ℝ) (hd : 0 < d)
    (hThreshold : θ * d ≤ δ) :
    0 ≤ δ / d - θ ∧
      Real.exp (-(δ / d - θ) * δ +
        d * (θ + (δ / d - θ))^2 / 2) =
      Real.exp (θ * δ - δ^2 / (2 * d)) := by sorry
