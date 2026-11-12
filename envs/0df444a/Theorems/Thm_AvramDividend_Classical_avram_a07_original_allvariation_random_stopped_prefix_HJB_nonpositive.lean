-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
-- name    : AvramDividend.Classical.avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:45:58.647508+00:00
-- url     : https://prove2.me/theorems/fc41ee99-11a4-4d6d-bed9-480b1b62e947
-- title:
--   Random stopped prefix of actual original HJB mesh has nonpositive drift
-- statement:
--   For every sample path, each grid index strictly before its random stopping index lies in the physical positive interior. The entire stochastic-clock prefix has nonpositive discounted generator drift plus dividend-gradient term. Uses true original admissibility, independent of bounded variation.
-- source:
--   Stopped-prefix specialisation of proved theorem 025d789c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_allvariation_random_stopped_prefix_HJB_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (k : Ω → ℕ)
    (hregion : ∀ ω i, i < k ω →
      0 < riskProcess X x D (u i) ω ∧
      ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    ∀ ω,
      (∑ i ∈ Finset.range (k ω),
        Real.exp (-(q * (u i : ℝ))) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) *
            (X.generator w (riskProcess X x D (u i) ω) -
              q * w (riskProcess X x D (u i) ω)) +
          (D (u (i + 1)) ω - D (u i) ω) *
            (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by sorry
