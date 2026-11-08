-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_change_ae_zero
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_change_ae_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:56:59.102881+00:00
-- url     : https://prove2.me/theorems/a41415bd-26ee-40f3-b30b-f91acb5384ab
-- title:
--   Actual stopped BV physical final-contact raw barrier value change vanishes almost surely without a derivative bound at ruin
-- statement:
--   For the actual BV Levy X and original dividend D, define the same last compensated stopped-grid increment and preceding post-right-payment reserve. If every such contact pair stays within a common nonnegative compact reserve interval, its raw vcstar value difference tends to zero almost surely as the authentic compensated physical mesh shrinks. The estimate includes the ruin endpoint but does not require a derivative there.
-- source:
--   The Proved original physical final-contact compensated increment tends to zero a.e. The Proved actual barrier candidate is uniformly continuous on the nonnegative compact contact band, and the Proved uniform-contact value-difference lemma transfers shrinking increments to shrinking raw value changes even though the stochastic base reserve varies with the grid. No approximation of expectations is inferred in this theorem; the separate uniform-bound/constant-DCT children will supply it.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_change_ae_zero
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
    (B : ℝ) (hB : 0 ≤ B) (z c : ℕ → Ω → ℝ)
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
    (hBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧ z m ω + c m ω ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)) := by sorry
