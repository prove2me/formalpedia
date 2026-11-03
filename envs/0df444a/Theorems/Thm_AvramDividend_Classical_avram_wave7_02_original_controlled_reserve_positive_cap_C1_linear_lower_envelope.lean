-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_controlled_reserve_positive_cap_C1_linear_lower_envelope
-- name    : AvramDividend.Classical.avram_wave7_02_original_controlled_reserve_positive_cap_C1_linear_lower_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:02:29.247431+00:00
-- url     : https://prove2.me/theorems/a5bfe0dd-e82e-44a0-b6e4-ec08e14b9353
-- title:
--   Original controlled reserve retains unit-slope C1 HJB lower envelope at strict positive-cap interior positions
-- statement:
--   For the exact original Avram controlled reserve under a standing spectrally negative Levy process and admissible dividend control, a nonnegative reserve strictly inside the cap obeys w(reserve)≥w(0)+reserve. It directly transfers the proven positive-cap unit-gradient theorem to the original Ω, P, X, filtration, riskProcess, x and D, without altering stochastic hypotheses or dividend measures.
-- source:
--   Source-faithful controlled-reserve adapter of Proved f138f64f-f82c-4fdc-943c-d77f480ba88f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_controlled_reserve_positive_cap_C1_linear_lower_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 ≤ riskProcess X x D t ω →
      ENNReal.ofReal (riskProcess X x D t ω) < C →
      w 0 + riskProcess X x D t ω ≤
        w (riskProcess X x D t ω) := by sorry
