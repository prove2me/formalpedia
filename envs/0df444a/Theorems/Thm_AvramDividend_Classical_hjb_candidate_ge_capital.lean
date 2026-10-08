-- Prove2me | Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
-- name    : AvramDividend.Classical.hjb_candidate_ge_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T23:24:38.72669+00:00
-- url     : https://prove2.me/theorems/674c0588-8af8-4a86-9fb1-09ca220768a3
-- title:
--   HJB supersolution dominates starting reserves on the capped domain
-- statement:
--   A verification candidate satisfying the dividend HJB condition has derivative at least 1 throughout the positive part of the reserve interval, so if w(0)≥0 then w(x)≥x≥0 for every initial capital x with 0≤x and ENNReal.ofReal x≤C. This isolates the non-negativity needed to discard the stopped terminal-value term in the Itô/localisation argument. It handles C=∞ and the finite cap boundary.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 4(i) and Equation (5.8), p. 17–19. Derive w'≥1 from max(Γw-qw,1-w')=0 and apply the mean-value theorem to w-id. The statement is a prerequisite for single-strategy verification theorem AvramDividend.Classical.admissible_cap_dividendValue_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.hjb_candidate_ge_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) :
    x ≤ w x := by sorry
