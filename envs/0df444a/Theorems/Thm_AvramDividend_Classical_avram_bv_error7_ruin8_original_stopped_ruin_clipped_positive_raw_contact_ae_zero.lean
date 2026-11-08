-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_raw_contact_ae_zero
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_raw_contact_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:24.350013+00:00
-- url     : https://prove2.me/theorems/4fad80ef-f590-4738-b619-77515db65b27
-- title:
--   Original BV stopped physical last-cell positive barrier-value error vanishes a.e. allowing ruin crossings
-- statement:
--   On the genuine bounded-variation Levy dividend process and the physical stopped grid, the positive part of the final raw vcstar value-change error converges almost surely to zero even when the last cell crosses below ruin, provided pre-contact and zero-clipped post-contact reserves remain in the same nonnegative compact localisation band.
-- source:
--   Proved original compensated final-cell mesh convergence, Proved original BV vcstar uniform continuity through zero, Proved ruin-crossing positive-value clipping majorant, and the independent clipped positive-contact convergence lemma. No BV signed expectation/prebudget or domination inferred from a.e. convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_raw_contact_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → Ω → ℕ)
    (hMesh : ∀ᵐ ω ∂P,
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       ∀ δ : ℝ, 0 < δ → ∀ᶠ m in Filter.atTop,
         ∀ i, i < k m ω →
           |Y (u m (i + 1)) - Y (u m i)| < δ))
    (B : ℝ) (z c : ℕ → Ω → ℝ)
    (hzSource : ∀ m ω, z m ω =
      if k m ω = 0 then 0 else
        x + X.X (u m (k m ω - 1)) ω -
          rightLimit D (u m (k m ω - 1)) ω)
    (hcSource : ∀ m ω, c m ω =
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       if k m ω = 0 then 0 else
         Y (u m (k m ω)) - Y (u m (k m ω - 1))))
    (hClipBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧
      max (z m ω + c m ω) 0 ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun m => max (Err m ω) 0)
      atTop (nhds (0 : ℝ)) := by sorry
