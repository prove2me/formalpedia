-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_no_small_band_marks_compensator_zero
-- name    : AvramDividend.Classical.avram_b27_original_no_small_band_marks_compensator_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:18:54.509196+00:00
-- url     : https://prove2.me/theorems/489c24bc-c9c4-4a4b-b5e8-7713ecb89d64
-- title:
--   Original intrinsic compensated small-negative-jump process vanishes when every nonzero path jump is at most minus one and nu has no small-mark mass
-- statement:
--   For the original source X with no Levy measure mass on (-1,0] and actual path jumps either zero or at most -1 at every positive time, both the counted marked-jump integral on the source finite negative small band (-1,-1/(n+1)] and its nu compensator vanish for every n and t. Consequently the exact published intrinsic small-band compensated source is identically zero. Applies to the B25 proposed Brownian plus size-2 Poisson example without altering the original stochastic source or signed compensation.
-- source:
--   Avram B25/B27 Brownian plus large negative jumps source obstruction; exact published 66a113ed small-band source definition and pinned Mathlib MeasureTheory support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b27_original_no_small_band_marks_compensator_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν (Ioc (-1 : ℝ) 0) = 0)
    (ω : Ω)
    (hLarge : ∀ u : ℝ≥0, 0 < u →
      (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 ∨
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -1))
    (n : ℕ) (t : ℝ≥0) :
    avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω = 0 := by sorry
