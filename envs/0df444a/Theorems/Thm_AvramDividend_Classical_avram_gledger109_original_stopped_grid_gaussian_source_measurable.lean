-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger109_original_stopped_grid_gaussian_source_measurable
-- name    : AvramDividend.Classical.avram_gledger109_original_stopped_grid_gaussian_source_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:35:48.316721+00:00
-- url     : https://prove2.me/theorems/905f10af-143c-4c47-b5b9-a05bd6289ff0
-- title:
--   Original finite-grid Gaussian physical source is measurable under the clipped stopping clock
-- statement:
--   The original stopped Gaussian source Finset sum is measurable on the original probability space for each mesh, using the original X and original right-limit dividend process; it is the missing independent measurable-source fact in gledger78.
-- source:
--   Extracts the standalone finite-grid measurability argument from gledger78 into a public child, reducing its 129-line proof to two independent pieces.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger109_original_stopped_grid_gaussian_source_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (r : ℕ) :
    Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((r : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      Finset.sum (Finset.range (r + 1)) (fun i =>
        (E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))))) := by sorry
