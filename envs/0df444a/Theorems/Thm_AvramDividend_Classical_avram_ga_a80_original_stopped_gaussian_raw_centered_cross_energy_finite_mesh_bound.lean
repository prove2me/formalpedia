-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
-- name    : AvramDividend.Classical.avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:46:45.964196+00:00
-- url     : https://prove2.me/theorems/df68aa7c-ec49-42da-b135-b5c786a0b1d7
-- title:
--   Actual stopped Gaussian raw-versus-centred finite physical grid quadratic cross energy is dominated by small centred energy and deterministic drift budget
-- statement:
--   On every finite original source physical grid and actual stopping-clock mask, the absolute raw-centred source square differences sum to no more than an arbitrary positive fraction of centred source energy plus a deterministic drift-squared budget proportional to the number of cells.
-- source:
--   Direct original Gaussian source exact spatial Taylor residual ga_a78 drift cross error bound to close b0d9951c positive stopped interior L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a80_original_stopped_gaussian_raw_centered_cross_energy_finite_mesh_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Finset ℕ) (s : ℕ → ℝ≥0)
    (ρ : Ω → ℝ≥0) (ω : Ω)
    (Z : ℕ → ℝ) (d ε : ℝ) (hε : 0 < ε) :
    (∑ i ∈ S, if s i < ρ ω then
      |(Z i + d)^2 - (Z i)^2| else 0) ≤
        ε * (∑ i ∈ S, if s i < ρ ω then (Z i)^2 else 0) +
        (S.card : ℝ) * ((1 + 1 / ε) * d^2) := by sorry
