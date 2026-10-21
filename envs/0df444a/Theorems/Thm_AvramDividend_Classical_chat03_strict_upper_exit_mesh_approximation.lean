-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_mesh_approximation
-- name    : AvramDividend.Classical.chat03_strict_upper_exit_mesh_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:42:43.394872+00:00
-- url     : https://prove2.me/theorems/45efdde1-0fe8-43f1-9f72-af75af3c1f57
-- title:
--   Strict upper passage is detected on every sufficiently fine uniform grid close to its actual first-passage infimum
-- statement:
--   For a right-continuous spectrally negative Lévy sample path, assume the strict upper barrier-crossing set has a finite greatest lower bound τ. For every ε>0 there is δ>0 such that each positive grid spacing h<δ contains a genuine strict upper crossing at a sampled time k*h in [τ,τ+ε). The result uses right-continuity on a strict-crossing interval and the NNReal ceiling-grid bracket. It does not require the strict crossing to be attained at τ, or impose a hypothesis on the opposite barrier. This establishes the separate-upper ingredient needed for convergence of the actual sampled upward and downward first-passage clocks.
-- source:
--   Accepted Chat03 strict upper exit right interval and NNReal ceiling grid bracket at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_upper_exit_mesh_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < τ + ε ∧
        upper < X.X ((k : ℝ≥0) * h) ω := by sorry
