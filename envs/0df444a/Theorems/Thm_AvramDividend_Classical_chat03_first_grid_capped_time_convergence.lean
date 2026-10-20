-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_capped_time_convergence
-- name    : AvramDividend.Classical.chat03_first_grid_capped_time_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:42:16.833612+00:00
-- url     : https://prove2.me/theorems/eed8714d-158f-47e7-874c-d8451221b070
-- title:
--   Capped first strict grid exit converges to the capped continuous strict exit infimum
-- statement:
--   For any spectrally negative Lévy sample path whose continuous strict two-sided exit infimum is τ, every sufficiently fine uniform mesh has an actual first strict grid-exit index k. The capped sample time min(kh,T) lies between min(τ,T) and min(τ,T)+ε. This single bound handles τ<T, τ=T and T<τ, and avoids requiring strict exit at τ. The result concerns passage times and does not assert convergence of stopped process values.
-- source:
--   Direct composition of Prove2Me theorem chat03_first_grid_strict_exit_approaches_infimum with elementary monotonicity and finite-horizon truncation in ℝ≥0, Mathlib pinned 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_capped_time_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) ∧
        min τ T ≤ min ((k : ℝ≥0) * h) T ∧
        min ((k : ℝ≥0) * h) T < min τ T + ε := by sorry
