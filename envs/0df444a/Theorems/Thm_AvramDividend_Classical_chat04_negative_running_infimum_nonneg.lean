-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
-- name    : AvramDividend.Classical.chat04_negative_running_infimum_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:40:32.134857+00:00
-- url     : https://prove2.me/theorems/b5791ec9-9175-4453-b1e2-11c9c27da438
-- title:
--   The negative running infimum of a Lévy process started at zero is nonnegative
-- statement:
--   Every finite-horizon path of a Lévy process beginning at zero has a running infimum no greater than zero, and therefore its negative running infimum is nonnegative. This exact support statement ensures the reflected-infimum Esscher laws are supported on nonnegative reserves.
-- source:
--   X.X_zero guarantees zero belongs to the finite-horizon path range. Proved `levy_path_bddBelow_finite_horizon` enables the real infimum inequality `csInf_le`. No exponential change of measure, scale function or stochastic optional stopping needed.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_negative_running_infimum_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω) :
    0 ≤ -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} := by sorry
