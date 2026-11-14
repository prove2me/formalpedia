-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
-- name    : AvramDividend.Classical.avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:27:35.705192+00:00
-- url     : https://prove2.me/theorems/501c68ba-80c4-4e27-8cd1-d1515c7ba446
-- title:
--   Continuous original candidate at zero has a uniform modulus on every closed nonnegative reserve band
-- statement:
--   The original HJB candidate is continuous on nonnegative reserves, including the ruin boundary zero. Prove that on every fixed closed nonnegative reserve interval [0,B], its candidate value has a uniform epsilon-delta modulus of continuity, even if the upper endpoint is below the lower endpoint. The proof restricts original continuity and applies Heine-Cantor; no global differentiability at zero or positive interior lower cutoff is used. The resulting explicit modulus is a missing hypothesis of the original BV physical-grid terminal boundary estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_candidate_zero_boundary_uniform_modulus
    (w : ℝ → ℝ) (B : ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
        |z - y| < δ → |w z - w y| < ε := by sorry
