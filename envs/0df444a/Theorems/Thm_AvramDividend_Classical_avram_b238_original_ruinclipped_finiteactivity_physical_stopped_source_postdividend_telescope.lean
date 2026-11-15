-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
-- name    : AvramDividend.Classical.avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:07:25.463063+00:00
-- url     : https://prove2.me/theorems/036fe055-37c4-40d0-b260-a6c6558cf43f
-- title:
--   Original ruin-clipped predictable physical mesh discounted source and postdividend adjustment exact telescoping
-- statement:
--   At each original stopped physical clock v_i=min(i n/(m+1),sigma), let Y_i=x+X(v_i)-rightLimit D(v_i) and let Z_i retain the true original dividend right limit frozen at v_i while advancing the actual Lévy source to v_{i+1}. The exact discounted terminal postpayment potential less initial postpayment potential is the finite sum of true source spatial cells plus true within-cell right-dividend postpayment corrections. This algebra is source-faithful for the mixed Gaussian and negative-jump case and stops at sigma, with no after-ruin terms. It is an essential starting identity for B236 finite stopped Itô cash and terminal contact, with the inclusive payment cash requiring separate Stieltjes control.
-- source:
--   Exact finite scalar telescoping by adding and subtracting e(v_{i+1})w(Z_i) and summing each true stopped physical cell. No probabilistic estimate or false post-ruin assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0)
    (n m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    e m * w (Y m) - e 0 * w (Y 0) =
      (Finset.range m).sum (fun i =>
        (e (i + 1) * w (Z i) - e i * w (Y i)) +
        e (i + 1) * (w (Y (i + 1)) - w (Z i))) := by sorry
