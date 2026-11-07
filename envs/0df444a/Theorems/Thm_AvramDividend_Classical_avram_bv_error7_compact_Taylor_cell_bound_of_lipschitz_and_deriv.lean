-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
-- name    : AvramDividend.Classical.avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:31:09.404053+00:00
-- url     : https://prove2.me/theorems/932673aa-e716-4235-b9af-7eaeee380da0
-- title:
--   Compact interior C1 Taylor error bounded globally by twice a common Lipschitz and derivative constant
-- statement:
--   On a fixed real compact interval, if a function has a global Lipschitz constant L≥0 and its derivative is bounded in absolute value by L, then for any pair of endpoints y and y+d whose full connecting interval lies inside that compact band, the exact first-order Taylor remainder is bounded by 2 L |d|. This removes the small-increment restriction in source-error domination once compact C1 implies the requisite finite derivative and Lipschitz bounds. It is a deterministic mathematical child, needed for the actual original BV grid error with potentially large early or contact-free cells.
-- source:
--   Triangle inequality for real absolute values, bounded derivative and a common Lipschitz constant on Set.Icc. Intended original-process consumer is a global C1 Taylor domination theorem composed with Proved BV-ERROR7 physical-grid variation b473d1e9 and A source L1 envelope 09287ead. This child makes no assertion about stochastic expectations or the BV prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (y d : ℝ)
    (hCell : Set.uIcc y (y + d) ⊆ Set.Icc a b) :
    |w (y + d) - w y - deriv w y * d| ≤ (2 * L) * |d| := by sorry
