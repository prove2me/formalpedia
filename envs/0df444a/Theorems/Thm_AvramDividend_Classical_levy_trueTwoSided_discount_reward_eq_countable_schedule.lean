-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_trueTwoSided_discount_reward_eq_countable_schedule
-- name    : AvramDividend.Classical.levy_trueTwoSided_discount_reward_eq_countable_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:59:16.963883+00:00
-- url     : https://prove2.me/theorems/41c09bd9-0009-478a-8449-cd338e786b3d
-- title:
--   True killed two-sided discounted exit reward equals the measurable countable-path reward
-- statement:
--   On each trajectory of a spectrally negative Lévy process, the discounted reward computed from exact strict upper and lower passage times agrees pathwise with the Borel countable-schedule reward. Consequently the stopped strong-Markov factorisation can use the measurable path functional without changing the two-sided exit event or its payoff.
-- source:
--   Direct consequence of verified two true-exit-to-countable-schedule clock identities; reward equality follows by substitution.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_strictLower_exit_subtype_inf_eq_schedule

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_trueTwoSided_discount_reward_eq_countable_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q upper lower : ℝ) :
    (let ρ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // upper < X.X t ω},
      (i.1 : ℝ≥0∞)
     let σ : ℝ≥0∞ := ⨅ i : {t : ℝ≥0 // X.X t ω < lower},
      (i.1 : ℝ≥0∞)
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) =
    (let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let ρ : ℝ≥0∞ := ⨅ j : ℕ,
       if upper < X.X (τ j) ω then (τ j : ℝ≥0∞) else ⊤
     let σ : ℝ≥0∞ := ⨅ j : ℕ,
       if X.X (τ j) ω < lower then (τ j : ℝ≥0∞) else ⊤
     if ρ < σ then ENNReal.ofReal (Real.exp (-(q * ρ.toReal))) else 0) := by sorry
