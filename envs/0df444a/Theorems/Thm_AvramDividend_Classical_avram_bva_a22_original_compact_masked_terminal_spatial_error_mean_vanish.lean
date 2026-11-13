-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
-- name    : AvramDividend.Classical.avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:41:49.485251+00:00
-- url     : https://prove2.me/theorems/69b6fbc6-6ffc-4af8-9e16-89361d705a03
-- title:
--   Original bounded-variation compactly localised true-horizon discounted terminal omission vanishes in expected positive error
-- statement:
--   For the original filtered bounded-variation spectrally negative Lévy process and actual physical uniform grid, define the positive extra discounted full-horizon terminal reward beyond the last grid time, masked to those paths where both original postpayment reserves lie inside one fixed strict compact and the later candidate value is nonnegative. Given integrability of this explicit positive error in each mesh row, show its expected value tends to zero for the original probability law. This follows from the exact uniform physical discounted drift bound and the genuine mesh gap convergence. The pathwise compact-mask branch is deterministic uniformly in sample, so no global generator integrability, artificial source or accelerated spatial bands are introduced. The unmapped boundary/ruin-contact region and measurability needed to establish each-row integrability remain separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc c d ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc c d ∧
          0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
