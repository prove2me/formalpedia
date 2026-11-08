-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_direct_discounted_contact_positive_L1
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_direct_discounted_contact_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:08:38.863148+00:00
-- url     : https://prove2.me/theorems/81830447-d4ad-4436-ac39-19032d856d60
-- title:
--   Original BV stopped-grid final contact discounted positive value error tends to zero with physical compensated mesh
-- statement:
--   For the original stopped BV spectrally negative Levy process and original admissible strategy, the physically discounted positive final raw vcstar contact error has an integrable positive part and expectation tending to zero under explicit compact nonnegative endpoint and measurability conditions.
-- source:
--   Use the Proved original compensated last-cell a.e. increment, Proved vcstar uniform continuity on [0,B], Proved uniform contact-difference vanishing, Proved original compact raw-value constant envelope, and Proved physical-discount positive-DCT. The proof does not import the BV signed prebudget or any theorem dependent on it. Source endpoint compactness and discounted measurability are explicit remaining localisation obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_discounted_final_contact_constant_DCT

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_direct_discounted_contact_positive_L1
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
    (Err Disc : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω))
    (hDiscSource : ∀ m ω, Disc m ω =
      Real.exp (-(q * (u m (k m ω - 1) : ℝ))) * Err m ω)
    (hDiscMeas : ∀ m, AEStronglyMeasurable (Disc m) P) :
    (∀ m, Integrable (fun ω => max (Disc m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Disc m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)):= by sorry
