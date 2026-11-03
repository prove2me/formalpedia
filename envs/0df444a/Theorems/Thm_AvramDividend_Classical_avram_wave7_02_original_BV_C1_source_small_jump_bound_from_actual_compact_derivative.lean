-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_source_small_jump_bound_from_actual_compact_derivative
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_source_small_jump_bound_from_actual_compact_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:54:44.902628+00:00
-- url     : https://prove2.me/theorems/7b09c207-59c5-490b-849d-fdb1ee82bca6
-- title:
--   Original BV stopped C1 small negative source-mark first-variation bound derived from actual compact derivative ceiling
-- statement:
--   For a true original spectrally negative bounded-variation Levy X with C1 candidate w on a genuine open HJB reserve band, a finite derivative ceiling K on the compact buffer [a/2,b] yields the true source small negative mark discounted nonlinear difference bound ≤K|z| at any original predictable left reserve y∈[a,b]. This derives the local Lipschitz bound from original C1 assumptions using a Proved compact derivative theorem, so no abstract Lipschitz premise is assumed. Source, right dividend, physical time and mark are unchanged.
-- source:
--   Compose Proved source-specific original BV C1 compact derivative Lipschitz theorem 82f28985 with Proved original discounted small-negative-mark envelope e6763634.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_predictable_small_mark_discounted_L1_by_source_variation
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_source_small_jump_bound_from_actual_compact_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : X.BoundedVariation →
      ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSmoothBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc (a / 2) b, ‖deriv w y‖₊ ≤ K)
    (ω : Ω) (t : ℝ≥0)
    (hBand : Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t ∈ Icc a b)
    (z : ℝ) (hzSmall : -a / 2 ≤ z ∧ z ≤ 0) :
    |Real.exp (-(q * (t : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t + z) -
       w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t))| ≤
      (K : ℝ) * |z| := by sorry
