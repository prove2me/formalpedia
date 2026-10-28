-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_shifted_trueTwoSided_reward_eq_schedule
-- name    : AvramDividend.Classical.levy_shifted_trueTwoSided_reward_eq_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:18:08.319405+00:00
-- url     : https://prove2.me/theorems/b65a4e1e-2df6-4d13-be58-3f751a63f7e5
-- title:
--   Every shifted Lévy future increment has its true killed two-sided reward on the measurable countable schedule
-- statement:
--   For any sample path, any nonnegative shift u and any two strict exit thresholds, the discounted upper-before-lower reward of the shifted future increment path X(u+t)-X(u) exactly equals the payoff computed from its natural-indexed countable observation schedule. This provides the pathwise identification needed to apply the proved finite-stopping-time strong Markov factorisation to killed reflected first-record regeneration.
-- source:
--   Compose the Proved generic right-persistent strict upper/lower exit clock identities with the shifted Lévy right-interval persistence lemmas, then substitute both clocks into the killed discounted reward.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_levy_shiftedLower_strictCrossing_rightInterval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_shifted_trueTwoSided_reward_eq_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (q upper lower : ℝ) :
    (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < g t},
       (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // g t < lower},
       (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let g : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ j : ℕ,
       if upper < g (τ j) then (τ j : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ j : ℕ,
       if g (τ j) < lower then (τ j : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by sorry
