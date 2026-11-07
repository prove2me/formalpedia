-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_C1_random_grid_event_positive_mean_vanishes
-- name    : AvramDividend.Classical.avram_bv_error7_original_C1_random_grid_event_positive_mean_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:33:48.170482+00:00
-- url     : https://prove2.me/theorems/48da63a8-ad5a-43f1-8491-057e9e596de6
-- title:
--   Original BV source C1 hypotheses imply event-localised sample-dependent physical positive Taylor error mean decay
-- statement:
--   For the exact original bounded-variation Lévy X and admissible D, the true sub-cap ContDiffOn ℝ 1 value-function condition suffices for the positive expected physical Taylor error to vanish on an arbitrary fixed interior localisation event, even where grid endpoints and cell counts are sample-dependent. The masked error is zero outside the event and assumed a.e. strongly measurable. All original J, Y and right-limit reserve source terms are preserved. On-event compact-band/mesh conditions are explicit, with L1 domination obtained from the genuine original BV path variation, no circular budget or invented process.
-- source:
--   Composes original source C1 compact regularity eecd0a2e-94ac-4e1a-8b44-2476caec3569 with event-local sample-dependent positive-error DCT child Z, an essential staging step to the original stopped-grid witness at cap/ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_C1_random_grid_event_positive_mean_vanishes
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
    (hMaskedMeas : ∀ m, AEStronglyMeasurable
      (fun ω => if ω ∈ s then Err m ω else 0) P) :
    (∀ m, Integrable (fun ω => max (if ω ∈ s then Err m ω else 0) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (if ω ∈ s then Err m ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
