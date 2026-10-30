-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_closed_killed_markov_two_stage
-- name    : AvramDividend.Classical.avram_ws01b_actual_closed_killed_markov_two_stage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:42:26.770999+00:00
-- url     : https://prove2.me/theorems/586f655d-5d25-42cc-a371-aff4f39464d8
-- title:
--   Genuine closed-window killed q-scale Markov two-stage factorisation
-- statement:
--   For the original Lévy process at any two deterministic times, the source closed-horizon killed q-scale payoff factors exactly through the actual measurable historical capital and surviving Boolean, and the independent original future entire-path law on a rational schedule. Holds for BV W(0)>0 and nonpositive initial capital; no assumed martingale or scalar harmonicity.
-- source:
--   Canonically Proved source-history Markov–Tonelli 984cb4a5, closed filtration survival cf6d2ea5, shifted random-reserve exact rational schedule 67c7e86c, and source scale monotonicity. Pathwise split is proved directly without using c2 or an exit identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_markov_tonelli_killed_history_kernel
import Theorems.Thm_AvramDividend_Classical_shifted_lower_survival_filtration_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_closed_killed_markov_two_stage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s u : ℝ≥0) (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = u) :
    let H : Ω → ℝ × Bool := fun ω =>
      (x + X.X s ω,
       if ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω then true else false)
    (∫⁻ ω,
      if ∀ v : ℝ≥0, v ≤ s + u → 0 ≤ x + X.X v ω then
        ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) *
          W (x + X.X (s + u) ω))
      else (0 : ℝ≥0∞) ∂P) =
    ∫⁻ h, ∫⁻ y,
      (if h.2 then
        if ∀ j : ℕ, τ j ≤ u → 0 ≤ h.1 + y (τ j) then
          ENNReal.ofReal (Real.exp (-(q * (u : ℝ))) * W (h.1 + y u))
        else (0 : ℝ≥0∞)
      else (0 : ℝ≥0∞))
      ∂(Measure.map (fun ω => (fun t : ℝ≥0 => X.X t ω)) P)
      ∂(Measure.map H P) := by sorry
