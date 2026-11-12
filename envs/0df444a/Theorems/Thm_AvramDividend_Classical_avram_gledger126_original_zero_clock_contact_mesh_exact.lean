-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger126_original_zero_clock_contact_mesh_exact
-- name    : AvramDividend.Classical.avram_gledger126_original_zero_clock_contact_mesh_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:14:48.842359+00:00
-- url     : https://prove2.me/theorems/6d171e40-3650-41a1-913b-36b50c36c291
-- title:
--   Original zero-clock stopped dividend-contact mesh cancels exactly
-- statement:
--   For the original source and original admissible dividend strategy at stopped time zero, the complete top-cap dividend-contact finite mesh cancels exactly for every mesh size and deterministic mesh width. The source and strategy start at zero, every clipped grid endpoint is zero, and the initial and terminal value corrections telescope.
-- source:
--   Actual source X(0)=0, actual admissible dividend D(0)=0, clipped mesh min(i times delta,0)=0, and finite sum of zero cell contact corrections. This is the zero-clock contact half of root-connected original gledger81.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger126_original_zero_clock_contact_mesh_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (q : ℝ) (Δ : ℝ≥0) (N : ℕ) :
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) 0
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range N, E (v (i + 1)) *
        ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
         (w (Y (i + 1)) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E 0 * (w (riskProcess X x D 0 ω) -
        w (x + X.X 0 ω - rightLimit D 0 ω)) = 0 := by sorry
