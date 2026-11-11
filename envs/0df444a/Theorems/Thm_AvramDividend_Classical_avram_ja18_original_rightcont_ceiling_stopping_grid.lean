-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_ceiling_stopping_grid
-- name    : AvramDividend.Classical.avram_ja18_original_rightcont_ceiling_stopping_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:04:11.76929+00:00
-- url     : https://prove2.me/theorems/5bb5d001-6784-495d-861c-cf6c84c0d697
-- title:
--   Original bounded right-continuous stopping admits adapted finite-horizon grid ceiling
-- statement:
--   A bounded original right-continuous stopping time can be rounded upwards to the first monotone deterministic grid time covering it. The minimal index is bounded, its level events are measurable at the corresponding original filtration grid times, and the physical stop lies below its rounded ceiling. This requires no Brownian or jump representation.
-- source:
--   Original-clock generic extraction of Proved avram_p4_e_true_ceiling_stop_exists_20261103 and its adapted-grid-index lemma. Direct Nat.find minimum and monotone e; supplies a useful genuine clock-grid child for 2d92580d original bounded optional stopping, independently of source reward.

import Mathlib
import Mathlib.Data.Nat.Find
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_rightcont_ceiling_stopping_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : ∀ ω, τ ω ≤ e N) :
    ∃ K : Ω → ℕ,
      (∀ ω, K ω ≤ N) ∧
      (∀ ω, τ ω ≤ e (K ω)) ∧
      (∀ i : ℕ,
        MeasurableSet[𝓕.rightCont (e i)] {ω | K ω ≤ i}) := by sorry
