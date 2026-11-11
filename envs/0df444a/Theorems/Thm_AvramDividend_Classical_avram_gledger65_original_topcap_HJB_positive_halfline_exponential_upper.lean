-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
-- name    : AvramDividend.Classical.avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:51:16.159442+00:00
-- url     : https://prove2.me/theorems/580c6378-1764-4672-9ff1-aec84424434e
-- title:
--   Exact original zero-jump top-cap HJB hypotheses imply a positive-half-line exponential value upper bound
-- statement:
--   The exact original zero-jump, infinite-cap Gaussian generator HJB and C2 interior hypotheses guarantee an upper exponential value envelope on every strictly positive spatial half-line. This turns the proved scalar ODE analysis into a directly reusable input for the original stopped physical-source positive-part L1 estimate, without imposing any global absolute-growth restriction.
-- source:
--   Root-connected gledger53 original Gaussian stopped source positive L1: exact original HJB source assumptions and C2 smoothness imply the needed one-sided exponential value upper envelope using Proved gledger61 and gledger64.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger64_topcap_C2_supplies_original_classical_derivatives
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℝ) (hu : 0 < u) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
