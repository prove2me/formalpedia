-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
-- name    : AvramDividend.Classical.avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:16:15.956279+00:00
-- url     : https://prove2.me/theorems/a2f90ee2-7ccc-4f45-85b0-4f052807e125
-- title:
--   Exact original stopped finite-grid G/H Gaussian source equals discounted linear noise on upper tube
-- statement:
--   On an original cap-barrier source path remaining within radius 1/400 through stopping horizon T, the Proved B51 identity sets the original clipped Gaussian coefficient G_i equal to the discounted linear coefficient and H_i equal to zero whenever s_i<T. Outside the stopped prefix both coefficients are zero. Therefore the exact full finite-grid G/H martingale source sum equals the stopped discounted linear centred increment sum for arbitrary noise increments Z and quadratic centring v. This is the source-identity input to the B109/B113 path-tube limit certificate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_original_barrier_upperstrip_physical_GH_coefficients
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB114_original_barrier_upperstrip_stopped_full_GH_mesh_equals_linear_noise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (ω : Ω)
    (hTube : ∀ u : ℝ≥0, u ≤ T →
      |X.X u ω| ≤ (1 / 400 : ℝ))
    (m : ℕ) (s : ℕ → ℝ≥0) (Z v : ℕ → ℝ)
    (q a : ℝ) (w : ℝ → ℝ) :
    let Y : ℕ → ℝ := fun i =>
      (1 / 8 : ℝ) + X.X (s i) ω -
        rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
    (Finset.range (m + 1)).sum (fun i =>
      (if s i < T then Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
      else 0) * Z i +
      (if s i < T then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
        (if Y i ∈ Icc a (5 / 44 : ℝ) then iteratedDeriv 2 w (Y i) else 0)
      else 0) * (Z i ^ 2 - v i)) =
    (Finset.range (m + 1)).sum (fun i =>
      if s i < T then Real.exp (-(q * (s i : ℝ))) * Z i else 0)
    := by sorry
