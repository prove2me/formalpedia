-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_inclusive_stopped_gaussian_source_L1
-- name    : AvramDividend.Classical.avram_p4_f3_original_inclusive_stopped_gaussian_source_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:31:48.658113+00:00
-- url     : https://prove2.me/theorems/6e2cc757-8d49-4160-9282-fba8e3d106f5
-- title:
--   Original inclusive stopped Gaussian source L1 from physical quadratic energy and original adaptedness
-- statement:
--   On the actual spectrally negative Lévy process X and original dividend strategy D, the inclusive physical stopping graph is measurable and the discounted Gaussian Ito coefficient is integrable on any finite physical source measure restricted to that stopping graph. This uses pinned original process measurability and finite quadratic energy, not an auxiliary equal-in-law process.
-- source:
--   Use Proved Gaussian source measurability 9befa605, finite L2 to L1 source 74d7cc2e, and finite restriction of μ. Independent of the canonical fdb/0dda targets.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_coefficient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_inclusive_stopped_gaussian_source_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤)
    (τ : Ω → ℝ≥0) (hτmeas : Measurable τ) :
    let S : Set (ℝ≥0 × Ω) := {p | p.1 ≤ τ p.2}
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    MeasurableSet S ∧ Integrable (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) (μ.restrict S) := by sorry
