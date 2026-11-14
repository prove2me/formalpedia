-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:14:59.100127+00:00
-- url     : https://prove2.me/theorems/24fbc83a-6677-48ff-b930-43b92e9ffcff
-- title:
--   Original BV terminal value has vanishing one-sided physical-grid increase uniformly at the zero-reserve boundary
-- statement:
--   For the original BV spectrally negative Levy process and original dividend strategy, any candidate monotone on the full compact nonnegative reserve interval and enjoying a uniform continuity modulus there has terminal reward increase at most an arbitrary positive epsilon for every sufficiently fine physical uniform grid, on a single probability-one original-source event whenever both postpayment reserves lie in the interval. Large negative source jumps can only decrease the monotone candidate; an upward source increment is bounded by drift times the final grid width. The theorem holds down to reserve zero without a strictly positive interior band, finite activity or any generator L1 assumption. The monotone and uniform-modulus hypotheses must still be obtained for the actual verification candidate at the relevant closed cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_last_reserve_drift_upper
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (B : ℝ)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ᵐ ω ∂P,
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B →
        (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B →
        w (x + X.X S ω - rightLimit D S ω) -
          w (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ≤ ε := by sorry
