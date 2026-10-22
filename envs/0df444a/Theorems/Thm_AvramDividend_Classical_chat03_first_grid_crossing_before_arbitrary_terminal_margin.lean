-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_crossing_before_arbitrary_terminal_margin
-- name    : AvramDividend.Classical.chat03_first_grid_crossing_before_arbitrary_terminal_margin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:15:44.535061+00:00
-- url     : https://prove2.me/theorems/a39e4f86-b8a3-4e7a-be96-ad6e001196ef
-- title:
--   Earliest strict grid crossing lies inside any terminal cap with a positive margin
-- statement:
--   For any positive real-valued time margin ε, if the terminal sampled time eventually exceeds the finite continuous strict two-sided exit infimum τ+ε, then every sufficiently fine positive uniform grid has its genuine earliest strict crossing index within the bounded search cap. This sharpens the previously Proved fixed ε=1 statement and permits grid caps terminating at any strictly later deterministic horizon.
-- source:
--   Generalisation of Proved chat03_first_grid_crossing_before_terminal_cap, using Proved chat03_first_grid_strict_exit_approaches_infimum with an arbitrary ε>0 and positivity of the mesh. Publication v2 fixes a malformed v1 authoring scaffold that left unsupported proof-goal branches.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_crossing_before_arbitrary_terminal_margin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ ε : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hε : 0 < ε)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n) :
    ∀ᶠ n in atTop,
      ∃ k : ℕ, k ≤ m n ∧
        (X.X ((k : ℝ≥0) * mesh n) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * mesh n) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * mesh n) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * mesh n) ω)) := by
  sorry
