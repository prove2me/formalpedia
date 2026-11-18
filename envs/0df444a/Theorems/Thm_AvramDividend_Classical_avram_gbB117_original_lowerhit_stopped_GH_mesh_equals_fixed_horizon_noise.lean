-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
-- name    : AvramDividend.Classical.avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:24:18.205385+00:00
-- url     : https://prove2.me/theorems/53c41f46-9a42-4e6a-ac31-f49e3014ff13
-- title:
--   Original lower-cutoff stopping-time Gaussian G/H mesh equals fixed-horizon linear source
-- statement:
--   For the original capped lower-cutoff first-hit stopping clock rho, the Proved B40 exact tube stopping-clock identity gives rho(omega)=T. The Proved B114 upper-strip coefficient theorem therefore identifies the exact G/H physical-grid source stopped at rho with the fixed-horizon discounted linear noise source, including all grid endpoints and quadratic centring terms. This bridge preserves the actual random stopping clock used in the original positive-stop cash source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB40_barrier_lower_hit_clock_equals_horizon_on_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (ρ : Ω → ℝ≥0)
    (hρ : ρ ω =
      sInf ((Icc (0 : ℝ≥0) T ∩
        (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω)) ⁻¹'
          Ici (-(5 / 44 : ℝ))) ∪ {T}))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z v : ℕ → ℝ)
    (q a : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < ρ ω then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
      else 0) * Z i +
      (if s i < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w (Y i) else 0)
      else 0) * (Z i ^ 2 - v i)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by sorry
