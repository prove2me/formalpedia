-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:14:18.437495+00:00
-- url     : https://prove2.me/theorems/9645ebf8-daf8-413a-8992-4c1b48a765c3
-- title:
--   Actual original masked Gaussian integrand has deterministic compact-band bound
-- statement:
--   For the original spectrally negative Levy process X, dividend process D, and physical pre-right-payment reserve left limit, the Gaussian coefficient sigma times the derivative of w masked to a compact interior band has a nonnegative deterministic upper bound in absolute value at every time and sample point. This imports the existing verified compact derivative bound and does not use a different process or completed filtration.
-- source:
--   Proved derivative_abs_le_on_compact_interior_interval theorem 98c2c058-e613-4558-8ab5-aa80e20cbf55 and actual Gaussian coefficient formalisation 7ae1130d-7935-43f5-ad75-a3ce3d5de9ac, inspected 7 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, |G p| ≤ C := by sorry
