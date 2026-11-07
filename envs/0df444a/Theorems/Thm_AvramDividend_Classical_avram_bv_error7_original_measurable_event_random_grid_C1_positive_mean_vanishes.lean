-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_measurable_event_random_grid_C1_positive_mean_vanishes
-- name    : AvramDividend.Classical.avram_bv_error7_original_measurable_event_random_grid_C1_positive_mean_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:37:27.840589+00:00
-- url     : https://prove2.me/theorems/bc68d3d7-0cce-4f4f-a388-9e1f040b4121
-- title:
--   Original BV stopped random physical C1 positive error vanishes in mean on measurable interior events
-- statement:
--   For the exact original bounded-variation spectrally negative Levy X and admissible dividend D, and random stopped physical grids with sample-dependent endpoints and cell counts, derive expected positive C1 Taylor error convergence on any measurable interior localisation event s. The only measurability assumption is a.e. strong measurability of the genuine unmasked physical error; the masked error is automatically measurable from the event and the pinned Mathlib indicator lemma. Interior compact C1 cell bands and shrinking Y increments are required only on s. Both L1 domination and DCT use the authentic original BV source mass, with no circular use of signed prebudget and no surrogate law.
-- source:
--   Integrates source-specific event-local original C1 positive DCT child AA and independent masked-error measurable child BB, yielding the clean event-localisation adapter needed by the original stopped-grid witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_measurable_event_random_grid_C1_positive_mean_vanishes
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → Ω → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hGrid : ∀ m ω, u m ω 0 = 0 ∧ u m ω (k m ω) = T ∧
      (∀ i, i < k m ω → u m ω i ≤ u m ω (i + 1)))
    (s : Set Ω)
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℝ := fun i => Y (u m ω (i + 1)) - Y (u m ω i)
       ∑ i ∈ Finset.range (k m ω),
         Real.exp (-(q * (u m ω i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P, ω ∈ s →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m ω i) ω - rightLimit D (u m ω i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m ω (i + 1)) - Y (u m ω i)
       (∀ m i, i < k m ω →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m ω → |c m i| < δ)))
    (hsMeas : MeasurableSet s)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (if ω ∈ s then Err m ω else 0) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (if ω ∈ s then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
