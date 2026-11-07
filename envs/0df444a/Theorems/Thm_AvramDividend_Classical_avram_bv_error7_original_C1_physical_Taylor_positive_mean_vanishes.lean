-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_C1_physical_Taylor_positive_mean_vanishes
-- name    : AvramDividend.Classical.avram_bv_error7_original_C1_physical_Taylor_positive_mean_vanishes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:51:57.539302+00:00
-- url     : https://prove2.me/theorems/ecf4c767-ebc2-4ed6-8db5-1ec3c94da897
-- title:
--   Original stopped BV grid positive Taylor error converges in expectation under the original C1 value-function hypotheses
-- statement:
--   For the authentic original bounded-variation SpectrallyNegativeLevy and admissible dividend process, its exact discounted physical-grid C1 Taylor residual has integrable positive part with expectation converging to zero under C1 on the positive sub-cap interior, a common compact interior cell band, almost-sure shrinking physical Y cells and residual measurability. The compact Lipschitz and derivative bounds are derived from original C1, not assumed. The full ruin/horizon contact, time-zero dividend and cap-boundary cells remain independent source obligations.
-- source:
--   Original physical-grid mean convergence 681ee517-e5bc-46f2-89ff-71af953f71e3 and original C1 compact Lipschitz adapter published via job 9fe8e345-ad57-4f96-bccd-9cf59f91e308. Neither imports the BV prebudget, signed expectation, or Fatou target.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_C1_physical_Taylor_positive_mean_vanishes
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
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hGrid : ∀ m, u m 0 = 0 ∧ u m (k m) = T ∧
      (∀ i, i < k m → u m i ≤ u m (i + 1)))
    (Err : ℕ → Ω → ℝ)
    (hSource : ∀ m ω, Err m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℝ := fun i => Y (u m (i + 1)) - Y (u m i)
       ∑ i ∈ Finset.range (k m),
         Real.exp (-(q * (u m i : ℝ))) *
           (w (z i + c i) - w (z i) - deriv w (z i) * c i)))
    (hPath : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℕ → ℝ := fun m i =>
         x + X.X (u m i) ω - rightLimit D (u m i) ω
       let c : ℕ → ℕ → ℝ := fun m i =>
         Y (u m (i + 1)) - Y (u m i)
       (∀ m i, i < k m →
         Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) ∧
       (∀ δ : ℝ, 0 < δ →
         ∀ᶠ m in Filter.atTop, ∀ i, i < k m → |c m i| < δ)))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
