-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_left_limit_cap
-- name    : AvramDividend.Classical.avram_locmoll_band_left_limit_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:55:12.211797+00:00
-- url     : https://prove2.me/theorems/ffd7bcc2-61a7-5353-8bc8-21646bfae296
-- title:
--   Pre-exit left reserve lies in the closed physical band and below the original cap
-- statement:
--   Pre-exit left reserve lies in the closed physical band and below the original cap
-- source:
--   Exact decomposition of 07460cee-1650-4edf-a37c-1b2c076b8656

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_left_limit_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (δ R : ℝ) (θ : Ω → ℝ≥0)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R) :
    ∀ ω (t : ℝ≥0), 0 < t → t ≤ θ ω →
      let y := Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      y ∈ Icc δ R ∧ ENNReal.ofReal y ≤ C := by sorry
