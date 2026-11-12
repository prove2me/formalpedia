-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
-- name    : AvramDividend.Classical.avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:29:40.559543+00:00
-- url     : https://prove2.me/theorems/09747a48-6cc1-42cf-b180-d0f5e4e056ac
-- title:
--   Exact original stopped finite-grid jump-compensator identity on the no-negative-marks event
-- statement:
--   For the physical original marked-jump measure, under zero negative marks before the horizon, the actual ruin-clipped and reserve-capped negative jump term vanishes for every grid index. Thus the signed compensated jump ledger equals minus its compensator exactly, retaining the true stop-time and pre-horizon mask.
-- source:
--   Original BV zero-count deterministic Stieltjes cash ledger 85b63af5 and Proved phys78

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys78_original_zero_marks_strict_horizon_grid_jump_term_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original marked-jump contribution to the stopped finite-grid ledger,
on an event with no negative marks, is exactly minus its compensator. -/

theorem AvramDividend.Classical.avram_bvb_phys79_original_zero_marks_stopped_marked_jump_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (C : ℝ≥0∞) (q : ℝ) (w : ℝ → ℝ)
    (U : ℝ≥0 → Ω → ℝ)
    (hZero : ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) :
    let H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < (T : ℝ) - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧
         p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ n : ℕ,
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) =
      -(∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) := by sorry
