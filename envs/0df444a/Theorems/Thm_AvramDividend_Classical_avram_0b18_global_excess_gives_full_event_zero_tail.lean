-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_0b18_global_excess_gives_full_event_zero_tail
-- name    : AvramDividend.Classical.avram_0b18_global_excess_gives_full_event_zero_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T12:13:16.102194+00:00
-- url     : https://prove2.me/theorems/318b264e-2b09-4b1d-b91b-eb41f66d34c0
-- title:
--   Global vanishing positive residual implies eventual full-event localisation and zero off-event tail
-- statement:
--   If the global expectation of the positive part of a sequence of residual errors tends to zero, choose every localisation event to be the full sample space and the fixed tail constant to be zero. The on-event expectation then retains the global limit and the off-event positive residual vanishes pointwise. This source-agnostic lemma is the precise noncircular implication needed when a global original compensated BV residual estimate is eventually established independently.

import Mathlib
open Classical MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_0b18_global_excess_gives_full_event_zero_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E R : ℕ → Ω → ℝ)
    (hGlobal : Tendsto
      (fun n => ∫ ω, max (E n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    ∃ s : ℕ → Set Ω, ∃ K : ℝ,
      0 ≤ K ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      Tendsto
        (fun n => ∫ ω, max (if ω ∈ s n then E n ω else 0) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P,
        max (if ω ∉ s n then E n ω else 0) 0 ≤
          (if ω ∈ s n then 0 else K * R n ω)) := by sorry
