-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_contact_L1
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_contact_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:32:28.466193+00:00
-- url     : https://prove2.me/theorems/816ffa08-4fc7-44bf-b76e-0ab985e2df50
-- title:
--   Original BV stopped ruin-crossing positive contact error has integrable positive part and expectation tending zero
-- statement:
--   For an original bounded-variation spectrally negative Levy process and admissible dividend strategy, under original source grid mesh, exact source reserve/increment definitions, compact pre-reserve and clipped post-reserve localisation, and positive-error measurability, the positive last-contact value error is integrable and its expectation tends to zero despite ruin crossings.
-- source:
--   Original ruin-clipped positive contact a.e.-convergence; original uniform clipped raw-error constant domination; and original Levy-probability positive DCT. The source assumptions are explicit. There is no import of the signed BV prebudget, canonical generator upper inequality or circular finite-grid budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_stopped_ruin_clipped_positive_contact_L1
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
      vcstar W (z m ω + c m ω) - vcstar W (z m ω))
    (hPosMeas : ∀ m, AEStronglyMeasurable (fun ω => max (Err m ω) 0) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
