-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_shifted_future_reserve_survival_measurable
-- name    : AvramDividend.Classical.chat04_countable_shifted_future_reserve_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:25:15.01999+00:00
-- url     : https://prove2.me/theorems/a484bed3-0181-498a-89db-b320f9ae3bcd
-- title:
--   Joint Borel measurability of shifted-reserve survival on a countable future schedule
-- statement:
--   A future increment path y and a current reserve r jointly determine nonruin on any countable monitoring schedule τ up to horizon T through r+y(τ_j)≥0. This subset of the product space ℝ×(ℝ≥0→ℝ) is Borel measurable. Crucially the reserve threshold is a variable state, rather than a fixed barrier as in Proved chat04_countable_future_path_barrier_survival_measurable. This is the measurable killing event required to apply the unconditional whole-future-path Markov–Tonelli theorem 77ced690-a2a9-4d93-bb66-4ae69a114152 to q-scale renewal semigroup approximations for a885f0b3; convergence from dense schedules is already formalised separately.
-- source:
--   Pinned Mathlib measurable_pi_apply, isClosed_Ici.measurableSet.preimage, MeasurableSet.iInter; generalises the previous Proved e1e2fc1f-6873-48e7-a160-d5352db19467 to jointly random starting reserve and future path, upstream of two-sided exit 3e1ce2c8.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_countable_shifted_future_reserve_survival_measurable
    (τ : ℕ → ℝ≥0) (T : ℝ≥0) :
    MeasurableSet
      {z : ℝ × (ℝ≥0 → ℝ) |
        ∀ j : ℕ, τ j ≤ T → 0 ≤ z.1 + z.2 (τ j)} := by sorry
