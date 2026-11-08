-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_mark_allpath_positive_ruin_time
-- name    : AvramDividend.Classical.avram_e0_initial_mark_allpath_positive_ruin_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:56:35.621199+00:00
-- url     : https://prove2.me/theorems/cd3e6728-a8d9-41c8-9399-307f374d4957
-- title:
--   An affordable nonnegative initial dividend leaves strictly positive ruin time on every continuous zero-start path
-- statement:
--   Every sample path starting at zero and continuous at the origin has a strictly positive first-survival interval after an affordable nonnegative initial dividend. The all-path statement combines the corrected local-reserve lemma with the original ruin-time infimum criterion; it supplies the exact source hruin premise in the proved first-grid nonintegrability obstruction.
-- source:
--   Source-exact bridge: corrected local reserve de475cd8 and original positive ruinTime 8ff20e24; target e0b94d7f first physical grid cell.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_mark_allpath_positive_ruin_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKstrict : ∀ ω, K ω < x)
    (hzero : ∀ ω, X.X 0 ω = 0)
    (hcont : ∀ ω, ContinuousAt (fun t : ℝ≥0 => X.X t ω) 0) :
    ∀ ω, (0 : ℝ≥0∞) <
      ruinTime X x (fun t η => if t = 0 then 0 else K η) ω := by sorry
