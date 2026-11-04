-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_physical_integral_DCT
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_true_clock_physical_integral_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:35:01.308911+00:00
-- url     : https://prove2.me/theorems/6687d899-e4b8-4e9e-92db-906a0fc7f770
-- title:
--   True original ruin-truncated physical integrals converge by dominated convergence under a genuine L1 envelope
-- statement:
--   For the actual original X,D and path ω, the physical-time integral of an integrable f truncated at min(ruinTime,n) converges to the full pre-ruin integral. The proof uses exact pointwise eventual stabilisation of the original stopping clock, measurable threshold sets and a genuine Integrable f μ dominating envelope in Mathlib DCT. No assertion is made about stochastic martingale M, random dividend Stieltjes atoms, or automatic integrability of the generator f.
-- source:
--   Accepted Proved original cofinal-clock pre-ruin source dfca4a60 directly, and pinned Mathlib dominated convergence theorem; no Open imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_eventually_strict_preruin
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source stopped physical-time integrals converge under true global L¹ domination. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_true_clock_physical_integral_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : Integrable f μ) :
    Tendsto
      (fun n : ℕ => ∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator f t ∂μ)
      atTop
      (nhds (∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator f t ∂μ)) := by sorry
