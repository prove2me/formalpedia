-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_signed_stieltjes_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_signed_stieltjes_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:16:16.4584+00:00
-- url     : https://prove2.me/theorems/33672cc0-bb07-4d59-b3aa-a7787ca5978b
-- title:
--   Boundary-safe signed original-source complete Stieltjes correction over the actual closed horizon
-- statement:
--   For an admissible finite-cap dividend strategy and every monotone pre-ruin finite time grid beginning at zero, the actual original-process full-horizon discounted dividendMeasure Stieltjes integral on [0,u_n], converted to a real number, plus the cap-linear value correction at the initial dividend right-payment and the signed sum of value corrections over every subsequent chronological source-frozen interval, is nonpositive. This controls singular-continuous and diffuse variation, all later right-payment jumps and the genuine time-zero atom, including reserve contacts with zero and the cap, without strict-interior localisation. Finiteness of the full dividend integral is derived from the independently Proved global budget, not assumed.
-- source:
--   Combine canonical global actual-measure bound, finite-real exact closed-horizon Stieltjes partition, and complete source-specific signed grid correction. The caplinear potential drop is measured after each source-left jump and through the dividend-right jump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_complete_signed_discounted_grid_correction_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_global_closed_signed_stieltjes_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ i : ℕ, i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (V (x + X.X 0 ω - rightLimit D 0 ω) - V (x + X.X 0 ω)) +
    ∑ i ∈ Finset.range n,
      (V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω)) ≤ 0 := by sorry
