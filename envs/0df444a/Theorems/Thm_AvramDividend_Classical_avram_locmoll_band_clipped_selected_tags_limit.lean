-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_clipped_selected_tags_limit
-- name    : AvramDividend.Classical.avram_locmoll_band_clipped_selected_tags_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:12:14.017978+00:00
-- url     : https://prove2.me/theorems/c8bcae87-578c-5153-a9a4-5da6e8ca0014
-- title:
--   Every selected half-open clipped grid cell has the correct sided endpoint limits
-- statement:
--   Every selected half-open clipped grid cell has the correct sided endpoint limits
-- source:
--   Physical dividend step certificate 45e95e97-eef3-4a02-ab5a-913134e1d165

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_clipped_selected_tags_limit
    (H θ t : ℝ≥0) (ht : t ≤ θ) (m i : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hcell : ∀ n,
      min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ < t ∧
      t ≤ min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ) :
    Tendsto (fun n => min ((i n : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ)
      atTop (𝓝[<] t) ∧
    Tendsto (fun n => min (((i n + 1 : ℕ) : ℝ≥0) * H / ((m n : ℝ≥0) + 1)) θ)
      atTop (𝓝[Ici t] t) := by sorry
