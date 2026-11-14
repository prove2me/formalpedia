-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb63_original_terminal_strip_drift_mark_and_compensator_joint_certificate
-- name    : AvramDividend.Classical.avram_bvb63_original_terminal_strip_drift_mark_and_compensator_joint_certificate
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:34:58.624447+00:00
-- url     : https://prove2.me/theorems/8e5ed0e1-7edc-4f94-b63d-48e393521ac9
-- title:
--   Original BV finite-activity physical last-strip drift increment, zero actual negative marks and arbitrarily small compensator intensity simultaneously
-- statement:
--   For the genuine original filtered bounded-variation finite negative jump intensity source and original exact prescribed physical uniform horizon grid, prove one conull event on which eventually, simultaneously: the actual last terminal cell has no negative source jump, its predictable negative-jump compensator intensity mass falls below every epsilon, and its actual X increment is precisely deterministic source drift times the physical terminal cell width. This source-faithful joint certificate is a direct input to BVB49 survivor/ruin and BVB59 expected cash-budget endpoint treatments.
-- source:
--   Already Proved original BVB50 physical drift terminal increment, BVB51 actual negative source count vanishing, and BVB52 original compensator intensity width zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb52_original_finite_negative_rate_times_uniform_last_strip_width_zero
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb63_original_terminal_strip_drift_mark_and_compensator_joint_certificate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, (u n (n + 1) : ℝ) =
      T - T / ((n : ℝ) + 2))
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 ∧
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2)) < ε ∧
      X.X S ω - X.X (u n (n + 1)) ω =
        ((S : ℝ) - (u n (n + 1) : ℝ)) * X.drift := by sorry
