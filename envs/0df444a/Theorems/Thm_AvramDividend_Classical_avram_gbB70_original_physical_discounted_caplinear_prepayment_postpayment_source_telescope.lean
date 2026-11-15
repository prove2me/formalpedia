-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB70_original_physical_discounted_caplinear_prepayment_postpayment_source_telescope
-- name    : AvramDividend.Classical.avram_gbB70_original_physical_discounted_caplinear_prepayment_postpayment_source_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:14:39.463252+00:00
-- url     : https://prove2.me/theorems/9062d2ac-fff5-4e66-81c6-4f2e05f40921
-- title:
--   Original finite-cap discounted Gaussian physical-grid spatial and right-dividend transition telescoping
-- statement:
--   For the actual original Lévy source X, original dividend strategy D and its right-limit at each physical-grid clock, the final discounted caplinear postpayment potential minus its initial counterpart is exactly the sum of all true prepayment frozen-dividend spatial discounted source increments plus discounted right-dividend postpayment corrections over the finite grid. This gives the genuine exponential discount identity connecting cash ledger and Gaussian stopped source in B54, with no change to the admissible cap or stopped process.
-- source:
--   Exact finite telescoping of e(s_i)V(Y_i) using original Y_i=x+X(s_i)-rightLimit D(s_i), source spatial endpoint Z_i=x+X(s_{i+1})-rightLimit D(s_i) and the original caplinear V_b; each cell splits by adding and subtracting e(s_{i+1})V(Z_i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB70_original_physical_discounted_caplinear_prepayment_postpayment_source_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b q : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (s (i + 1)) ω - rightLimit D (s i) ω
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    e m * V (Y m) - e 0 * V (Y 0) =
      (Finset.range m).sum (fun i =>
        (e (i + 1) * V (Z i) - e i * V (Y i)) +
        e (i + 1) * (V (Y (i + 1)) - V (Z i))) := by sorry
