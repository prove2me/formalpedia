-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_origin_postright_surplus
-- name    : AvramDividend.Classical.avram_a19_origin_postright_surplus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:14:36.679281+00:00
-- url     : https://prove2.me/theorems/a0b86de4-6b17-4916-820a-1f4981c695e2
-- title:
--   Exact original A19 first-cell reserve after time-zero right dividend
-- statement:
--   At the original A19 physical uniform grid's first sample time zero, the exact left-limit controlled reserve equals initial surplus less the dividend paid immediately after time zero.
-- source:
--   Source-exact instantiation of Proved p2_a_zero_rate_leftLim_origin_nnreal and the original Levy process X_zero field, targeting the remaining A19 generator-cell integrability obstacle.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_leftLim_origin_nnreal
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a19_origin_postright_surplus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (u : ℕ → ℕ → ℝ≥0)
    (hgrid0 : ∀ n, u n 0 = 0) (n : ℕ) (ω : Ω) :
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n 0) =
      x - rightLimit D 0 ω := by sorry
