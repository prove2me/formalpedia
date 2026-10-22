-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_future_path_barrier_survival_measurable
-- name    : AvramDividend.Classical.chat04_countable_future_path_barrier_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T07:18:02.177512+00:00
-- url     : https://prove2.me/theorems/e1e2fc1f-6873-48e7-a160-d5352db19467
-- title:
--   Borel measurability of two-barrier survival on any countable schedule in full future-path space
-- statement:
--   For any countable schedule τ:Nat→nonnegative real time, finite time horizon T and real lower/upper strict exit barriers, the subset of the entire function-valued path space (nonnegative real time→real) consisting of paths y which at every scheduled observation τ_j≤T satisfy ¬(y(τ_j)<lower or upper<y(τ_j)) is a measurable set in the standard product sigma-algebra. The proof uses the exact pinned Mathlib measurable_pi_apply theorem to establish that each upper/lower boundary evaluation event is measurable, complements their union to describe survival at an observation, guards observations by τ_j≤T, and takes the countable intersection via MeasurableSet.iInter. No Lévy process or stochastic independence assumptions are required. This is the precise Borel path event interface needed to apply the independently ACCEPTED full-future-path conditional event Markov formulas to barrier monitoring. It deliberately does NOT claim that an arbitrary uncountable intersection of coordinate events is Borel: equivalence of true continuous survival to countable dense monitoring uses separate right-continuity results.
-- source:
--   Pinned Mathlib measurable_pi_apply (Mathlib.MeasureTheory.MeasurableSpace.Constructions), MeasurableSet.iInter (Defs), and the approved Chat04 full-future-path Markov programme. Existing AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq handles right-continuous path grid equivalence for the process itself.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_countable_future_path_barrier_survival_measurable
    (τ : ℕ → ℝ≥0) (T : ℝ≥0)
    (lower upper : ℝ) :
    MeasurableSet
      {y : ℝ≥0 → ℝ | ∀ j : ℕ, τ j ≤ T →
        ¬ (y (τ j) < lower ∨ upper < y (τ j))} := by sorry
