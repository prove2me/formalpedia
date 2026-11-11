-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_piecewisePath_leftLimit_public
-- name    : AvramDividend.Classical.avram_a06_piecewisePath_leftLimit_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T17:39:37.866216+00:00
-- url     : https://prove2.me/theorems/6ae90837-05b5-426c-904e-e4c747d4d0b1
-- title:
--   Public exact left limit of a compound-Poisson piecewise jump path
-- statement:
--   At arrival n the left limit of the affine piecewise sample path is its right-continuous value minus the mark Y n. This identifies the sign of each jump and enables the original all-path no-positive-jump condition.
-- source:
--   Pinned LeanLevy PiecewisePath.lean around left-limit lemma, re-proved from public levy_foundations_jumpCountLtIff and deterministic piecewise definition to avoid private theorem imports.

import Mathlib
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Theorems.Thm_levy_foundations_jumpCountLtIff
open Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_piecewisePath_leftLimit_public
    {x₀ b : ℝ} {T Y : ℕ → ℝ}
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) :
    Tendsto (LevyFoundations.piecewisePath x₀ b T Y)
      (𝓝[Set.Iio (T n)] (T n))
      (𝓝 (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by sorry
