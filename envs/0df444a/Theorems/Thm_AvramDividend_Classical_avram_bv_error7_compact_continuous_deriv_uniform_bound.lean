-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_continuous_deriv_uniform_bound
-- name    : AvramDividend.Classical.avram_bv_error7_compact_continuous_deriv_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:40:54.109191+00:00
-- url     : https://prove2.me/theorems/472a3c0c-f020-4826-96e8-9a98aa195533
-- title:
--   Continuous original C1 derivative has a uniform nonnegative bound on a compact real band
-- statement:
--   A real-valued derivative continuous on a compact interval Icc a b is uniformly bounded in absolute value by some finite nonnegative real L. This is the precise compactness input needed to replace the extra uniform derivative-bound hypothesis in the original BV physical-grid global Taylor source envelope. It follows from the image of a compact set under a continuous function being bounded, including the empty-band case.
-- source:
--   Pinned Mathlib IsCompact.exists_bound_of_continuousOn gives real norm bound on compact Set.Icc. Derived from analytic compactness alone; intended downstream is a compact C1 Lipschitz adapter for original BV dividend w and eventually global Taylor source domination. No stochastic prebudget or surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_compact_continuous_deriv_uniform_bound
    (w : ℝ → ℝ) (a b : ℝ)
    (hDerCont : ContinuousOn (deriv w) (Set.Icc a b)) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L := by sorry
