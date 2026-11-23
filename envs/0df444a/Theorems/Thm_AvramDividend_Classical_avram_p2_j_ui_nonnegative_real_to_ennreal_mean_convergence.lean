-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
-- name    : AvramDividend.Classical.avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:51:38.157329+00:00
-- url     : https://prove2.me/theorems/db3e760e-855c-4492-b210-6ae56b780621
-- title:
--   Nonnegative Bochner expectation convergence lifts to genuine ENNReal lintegral convergence
-- statement:
--   For a measure P and an integrable sequence of nonnegative real random variables Y_n converging in real Bochner expectation to an integrable a.e. nonnegative Z, prove convergence of their actual ENNReal lintegral expectations. This gives the exact finite-mean bridge needed to compare bounded jump-count expectations to nonnegative intrinsic marked-count measures, without assuming a rate, probability normalisation, or L2 bound.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal

/-! An integrable nonnegative Bochner mean limit is the genuine ENNReal lintegral mean limit. -/

theorem AvramDividend.Classical.avram_p2_j_ui_nonnegative_real_to_ennreal_mean_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, Integrable (Y n) P) (hZ : Integrable Z P)
    (hYn : ∀ n, 0 ≤ᵐ[P] Y n) (hZn : 0 ≤ᵐ[P] Z)
    (hMean : Tendsto (fun n : ℕ => ∫ ω, Y n ω ∂P)
      atTop (nhds (∫ ω, Z ω ∂P))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (Y n ω) ∂P)
      atTop (nhds (∫⁻ ω, ENNReal.ofReal (Z ω) ∂P)) := by sorry
