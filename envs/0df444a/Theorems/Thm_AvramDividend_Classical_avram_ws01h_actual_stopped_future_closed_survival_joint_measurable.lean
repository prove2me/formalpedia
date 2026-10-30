-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
-- name    : AvramDividend.Classical.avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:12:20.785263+00:00
-- url     : https://prove2.me/theorems/844b8089-7996-4dda-ac22-7260acabdab0
-- title:
--   True original Lévy shifted closed-horizon nonruin of random stopped reserve is jointly measurable in path and real observation clock
-- statement:
--   For the actual source spectrally negative Lévy process and any measurable random finite stopping age τ, the event that the complete post-τ shifted Lévy future from reserve a remains nonnegative at every time up to residual real observation age (r−τ)^+ is jointly Borel measurable in original sample path and real observation clock. This is stronger than separate fixed-horizon measurability and does not assume arbitrary variable evaluation on uncountable cylinder path space: the canonically proved exact closed-horizon rational-grid equivalence reduces the event to the jointly measurable countable open-grid tests plus one measurable terminal X_(τ+T) observation. The former is measured via proved measurable whole shifted path and rational H, the latter via proved true Lévy joint state measurability. Enables genuine Qp per-path a.e. shifted future reward transfer and exact record-branch CDF renewal without any open exit identity.
-- source:
--   Proved original source shifted closed rational-grid iff fd37c55c; whole random-age shifted path measurable 8e59a363; countable H measurable 0b7edea5; joint Lévy time-state measurable d55462c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) (a : ℝ) :
    MeasurableSet {z : Ω × ℝ |
      0 ≤ z.2 ∧
      ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
        0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)} := by sorry
