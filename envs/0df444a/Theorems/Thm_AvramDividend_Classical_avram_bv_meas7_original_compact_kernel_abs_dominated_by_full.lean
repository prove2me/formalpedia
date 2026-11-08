-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_compact_kernel_abs_dominated_by_full
-- name    : AvramDividend.Classical.avram_bv_meas7_original_compact_kernel_abs_dominated_by_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:51:19.054196+00:00
-- url     : https://prove2.me/theorems/15cf5a72-dbdd-492f-88b4-7346168ece06
-- title:
--   Original stopped compact Lévy kernel is dominated by its full interior source
-- statement:
--   For the actual original spectrally negative Lévy X, dividend D, left-limit pre-right-payment reserve, finite ruin-stopped horizon, arbitrary negative jump mark, test value w and discount q, any compact reserve band with half-band lying strictly inside the positive cap has its discounted jump-value integrand bounded in absolute value by the corresponding full interior integrand. This supplies the pointwise domination needed for a later dominated convergence passage, conditional on proving the full source is integrable.
-- source:
--   Pointwise original-source conditional reduction using the exact same stopped clock and negative mark. If the compact mask is active, half-band inclusion implies the full cap mask and both kernels coincide. Otherwise the compact kernel is zero. Integrability of the full envelope is deliberately not assumed or asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_compact_kernel_abs_dominated_by_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (w : ℝ → ℝ) (q : ℝ) (S : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun r =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s r.2 - rightLimit D s r.2) r.1
    ∀ (p : ℝ≥0 × Ω) (z : ℝ),
      |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Z p ∈ Icc a b ∧ z < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
        else 0)| ≤
      |(if (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        0 < Z p ∧ ENNReal.ofReal (Z p) < C ∧ z < 0 then
        Real.exp (-(q * (p.1 : ℝ))) * (w (Z p + z) - w (Z p))
        else 0)| := by sorry
