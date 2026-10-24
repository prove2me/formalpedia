-- Prove2me | Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
-- name    : AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:51:34.996443+00:00
-- url     : https://prove2.me/theorems/5c6df1d9-08d7-4a57-b3fc-94f32588e34b
-- title:
--   Dyadic ceiling approximations converge in the stopping-time domain
-- statement:
--   For any nonnegative time t, its natural-number ceiling at dyadic resolution, divided by the positive dyadic scale as a nonnegative real, converges to t in the topology on ℝ≥0. The established real-valued convergence transfers along the topological embedding ℝ≥0→ℝ. This is the missing topology-level bridge from real dyadic rounding to the actual domain of stopping times in the bounded-stopping approximation theorem.
-- source:
--   Proved dyadic_ceiling_rounding_tendsto (eb5240c4-480a-4f01-a31c-d944c87b2b7b), and Mathlib NNReal.tendsto_coe in the pinned 0df444 revision.

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_tendsto
open Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n)
      atTop (𝓝 t) := by sorry
