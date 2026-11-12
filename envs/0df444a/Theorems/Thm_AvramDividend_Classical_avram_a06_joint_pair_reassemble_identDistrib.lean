-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_joint_pair_reassemble_identDistrib
-- name    : AvramDividend.Classical.avram_a06_joint_pair_reassemble_identDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:01:56.759207+00:00
-- url     : https://prove2.me/theorems/46e222f6-7153-4ce9-8903-861f6499e588
-- title:
--   Reassemble a waiting-time stream from independent first coordinate and tail law
-- statement:
--   A measurable deterministic reconstruction of an infinite stream from its head and complete suffix preserves equality in law of the pair. This is the last coordinate-assembly step for the A06 renewal residual process.

import Mathlib
open MeasureTheory ProbabilityTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_joint_pair_reassemble_identDistrib
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R U : Ω → ℝ) (F G : Ω → (ℕ → ℝ))
    (hPair : IdentDistrib (fun ω => (R ω, F ω))
      (fun ω => (U ω, G ω)) P P) :
    IdentDistrib
      (fun ω (j : ℕ) => if j = 0 then R ω else F ω (j - 1))
      (fun ω (j : ℕ) => if j = 0 then U ω else G ω (j - 1)) P P := by sorry
