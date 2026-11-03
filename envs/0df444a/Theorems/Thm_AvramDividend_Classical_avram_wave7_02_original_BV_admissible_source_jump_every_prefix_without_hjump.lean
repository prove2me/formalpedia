-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_admissible_source_jump_every_prefix_without_hjump
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_admissible_source_jump_every_prefix_without_hjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:24:04.923513+00:00
-- url     : https://prove2.me/theorems/23321dfb-cfd5-4396-8b48-b304d6d6ee00
-- title:
--   Every original BV source-jump finite prefix satisfies complete right atom budget with automatically derived HJB dividend jump
-- statement:
--   Under original source process X, original nondecreasing left-continuous dividends D, capped IsAdmissibleLe, C1 gradient and initial reserve cap, all finite prefixes of source-before-payment jumps have nonpositive discounted HJB corrections including the complete time-zero Stieltjes atom. The independent hjump premise of the previous source theorem is fully derived from canonical assumptions. The result does not assert a stochastic compensated limit.
-- source:
--   Direct composition of Proved a14aba30 finite-prefix source HJB budget and the independent canonical admissibility-to-hjump lemma, preserving actual process and control.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_arbitrary_source_jump_sequence_every_finite_prefix_full_initial_budget
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_admissible_source_jump_every_prefix_without_hjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x q : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℕ → ℝ≥0)
    (hTimes : ∀ n, 0 < t n ∧ (t n : ℝ≥0∞) < ruinTime X x D ω)
    (hValid : ∀ n,
      X.X (t n) ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t n) - D (t n) ω) ≤ C) :
    let J : ℕ → ℝ := fun i =>
      Real.exp (-(q * (t i : ℝ))) *
        ((w (x + X.X (t i) ω - rightLimit D (t i) ω) -
            w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) (t i) -
              D (t i) ω)) +
          (rightLimit D (t i) ω - D (t i) ω))
    ∀ n : ℕ, (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n, J i) ≤ w x := by sorry
