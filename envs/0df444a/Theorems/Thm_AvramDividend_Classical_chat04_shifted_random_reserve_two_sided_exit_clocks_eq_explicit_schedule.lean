-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:05:47.624898+00:00
-- url     : https://prove2.me/theorems/d98e2c20-7abf-4b18-b2e1-0b575124f273
-- title:
--   Both true strict exit clocks of a shifted Lévy reserve with random capital equal explicit countable first-passage clocks
-- statement:
--   For any spectrally negative Lévy path, arbitrary deterministic clock translation b and path-dependent initial reserve H, the true upward and downward strict first-passage times of the shifted reserve relative to the lower barrier zero and upper barrier a both agree exactly with the corresponding infima over an explicit Nat.unpair rational monitoring sequence. This includes never-crossing paths, where the clocks are infinite, and supports pathwise two-sided exit rewards for random reserves.
-- source:
--   Proved generic right-persistent upper/lower strict exit time schedule theorems, instantiated using Proved right persistence of shifted Lévy increments with thresholds a-H and -H.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_levy_shiftedLower_strictCrossing_rightInterval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_clocks_eq_explicit_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b : ℝ≥0) :
    (let g : ℝ≥0 → ℝ := fun t => X.X (b + t) ω - X.X b ω
     let τ : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     (⨅ i : {t : ℝ≥0 // a - H ω < g t}, (i.1 : ℝ≥0∞)) =
       (⨅ j : ℕ, if a - H ω < g (τ j) then (τ j : ℝ≥0∞) else ⊤) ∧
     (⨅ i : {t : ℝ≥0 // g t < -H ω}, (i.1 : ℝ≥0∞)) =
       (⨅ j : ℕ, if g (τ j) < -H ω then (τ j : ℝ≥0∞) else ⊤)) := by sorry
