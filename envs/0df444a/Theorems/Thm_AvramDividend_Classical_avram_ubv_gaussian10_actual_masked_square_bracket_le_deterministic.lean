-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:51:02.400033+00:00
-- url     : https://prove2.me/theorems/eb498a7c-d71f-43fe-b405-a147b266b78f
-- title:
--   Original masked Gaussian square bracket has all-path deterministic bound
-- statement:
--   The genuine original-process Gaussian coefficient, evaluated at the left-limit reserve and restricted to a compact interior band, has a deterministic upper bound on its finite-horizon square bracket for every sample path. Only finite time-mass and compact C1 regularity are needed; the original filtration and dividend process are retained exactly.
-- source:
--   Original masked Gaussian uniform bound 9645ebf8; uniform square bracket deterministic cap, pinned Mathlib norm_integral bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_square_bracket_le_deterministic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω,
      (∫ t in Ioc (0 : ℝ≥0) T, (G (t, ω)) ^ 2 ∂μtime) ≤
        C ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ := by sorry
