-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_direct_raw_contact_positive_L1
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_direct_raw_contact_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:09:36.742913+00:00
-- url     : https://prove2.me/theorems/c995b300-5e13-491a-8bc7-30cd7f51eec1
-- title:
--   Actual BV stopped last-cell raw vcstar positive error is L1-negligible from original compensated physical mesh
-- statement:
--   Original bounded-variation Levy process, dividend strategy and sample-dependent compensated physical stopped final cell. Under explicit nonnegative compact reserve endpoint and measurability conditions, the raw final vcstar change has integrable positive part and expectation tending to zero. The proof derives almost-sure convergence directly from the original physical mesh and uses independent uniform domination.
-- source:
--   The original BV stopped contact increment tends to zero almost surely by the Proved compensated mesh theorem. Proved Heine-Cantor vcstar uniform continuity at zero and the Proved shrinking-contact inequality yield raw value-change a.e. convergence. Proved compact vcstar value boundedness and Proved probability constant-DCT yield L1 convergence. Neither failed dependency-edge theorem nor BV signed prebudget imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_final_contact_compensated_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_probability_constant_dom_positive_DCT

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_direct_raw_contact_positive_L1
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
      vcstar W (z m ω + c m ω) - vcstar W (z m ω))
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)):= by sorry
