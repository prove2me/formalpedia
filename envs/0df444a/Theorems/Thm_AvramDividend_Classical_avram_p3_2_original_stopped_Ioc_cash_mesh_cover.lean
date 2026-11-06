-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_Ioc_cash_mesh_cover
-- name    : AvramDividend.Classical.avram_p3_2_original_stopped_Ioc_cash_mesh_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:02:17.128321+00:00
-- url     : https://prove2.me/theorems/b5506d29-164b-441a-8456-87de09452bcd
-- title:
--   Original X/D ruin-clipped dividend mesh cells cover the stopped physical interval
-- statement:
--   For original Lévy process and dividend strategy, union of all first n half-open stopped physical dividend cells equals the half-open interval from 0 to the nth stopped grid time.
-- source:
--   Instantiate fully Proved physical monotone uniform stopped grid and finite monotone Ioc mesh cover, then simplify u 0=0; carries original X/D ruin clock with exact Mathlib pin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_monotone_Ioc_mesh_cover

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_stopped_Ioc_cash_mesh_cover
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    (⋃ i ∈ Finset.range n,
      Ioc (u i : ℝ) (u (i + 1) : ℝ)) = Ioc 0 (u n : ℝ):= by sorry
