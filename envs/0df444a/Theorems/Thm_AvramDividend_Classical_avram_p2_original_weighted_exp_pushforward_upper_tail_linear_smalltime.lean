-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime
-- name    : AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:12:19.05587+00:00
-- url     : https://prove2.me/theorems/9c138796-14a8-4c66-8615-ef82911b9d78
-- title:
--   Original fourth-weighted exponential pushforward obeys uniform Markov upper-tail O(h)
-- statement:
--   The first moment of the actual fourth-deficit-weighted exp(X_h) pushforward is O(h). Applying the pinned Mathlib Markov inequality to the nonnegative mark z gives a uniform bound on a times the original weighted mass of all z with a≤max(z,0). This is the concrete positive-tail control needed before the method-of-moments compactness argument; no Poisson or conditional jump-rate assumption is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ a : ℝ≥0∞,
          a * ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
              {z : ℝ | a ≤ ENNReal.ofReal z} ≤
          ENNReal.ofReal (C * h) := by sorry
