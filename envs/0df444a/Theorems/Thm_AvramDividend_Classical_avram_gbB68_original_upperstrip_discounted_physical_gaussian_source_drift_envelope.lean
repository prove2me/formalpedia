-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
-- name    : AvramDividend.Classical.avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:10:39.084245+00:00
-- url     : https://prove2.me/theorems/0afc1089-0549-4883-b079-78ee8421152d
-- title:
--   Original physical upper caplinear source cell discounted centred Gaussian remainder bounded by actual positive drift occupation
-- statement:
--   On every genuinely original physical Gaussian source cell with both predividend reserve endpoints above interior clip b, the discounted caplinear spatial source increment minus the authentic centred Gaussian increment is bounded by the original physical time step times positive drift max(X.c,0). This identifies the exact upper-strip cell contribution to the prepayment occupation HJB budget of the B54 stopped Itô cash estimate, keeping source X and dividend rightLimit D unchanged.
-- source:
--   Proved B67 exact original centred Gaussian upper affine source identity gives Δ X.c. Multiply by positive original discount exp(-qs), then bound X.c≤max(X.c,0) with Δ≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB67_original_caplinear_upper_strip_physical_centered_gaussian_source_drift
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB68_original_upperstrip_discounted_physical_gaussian_source_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let Y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X (s + Δ) ω - rightLimit D s ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let centred : ℝ :=
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    b < Y → b < Z →
      Real.exp (-(q * (s : ℝ))) * (V Z - V Y - centred) ≤
        Real.exp (-(q * (s : ℝ))) * (Δ : ℝ) * max X.c 0 := by sorry
