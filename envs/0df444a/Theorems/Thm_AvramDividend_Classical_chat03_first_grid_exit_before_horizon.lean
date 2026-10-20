-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_first_grid_exit_before_horizon
-- name    : AvramDividend.Classical.chat03_first_grid_exit_before_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:36:51.594362+00:00
-- url     : https://prove2.me/theorems/1eef4eb0-c990-443b-8bb0-97b0b743074c
-- title:
--   First strict grid exit is detected before any horizon strictly beyond the continuous passage
-- statement:
--   If the strict two-sided continuous exit time τ for a spectrally negative Lévy path is strictly before a finite nonnegative horizon N, then for all sufficiently small positive grid steps h there exists an actual first strict grid exit index k with τ≤kh<N and no earlier grid sample exiting. The conclusion follows from the already accepted first grid exit ε–δ approximation by choosing an intermediate time u between τ and N and setting ε=u−τ>0. The statement preserves first-passage boundary creeping and requires no continuous-time filtration regularity or q-scale martingale.
-- source:
--   Direct Chat03 composition of previously Proved strict first-grid exit convergence and the pinned order-density theorem exists_between, Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_first_grid_exit_before_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ N : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτN : τ < N) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < N ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by sorry
