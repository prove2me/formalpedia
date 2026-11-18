-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
-- name    : AvramDividend.Classical.avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:48:30.022339+00:00
-- url     : https://prove2.me/theorems/925223dd-fc7f-4574-a4ff-056e1340d37b
-- title:
--   Any uniform continuous-path tube up to 17/16000 bounds all source samples up to 1/1000 in NNReal time
-- statement:
--   For any function f on nonnegative real time, a uniform pointwise bound f_u≤R for all unitInterval times u≤17/16000 transfers to every true source time t≤1/1000 by embedding t into unitInterval and identifying its NNReal lift. This deterministic source-time bridge simultaneously handles centred and drifted Brownian tube bounds needed for original stopped-cash proofs, without importing any Gaussian source model or requiring path measurability.

import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.NormNum
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_unitInterval_early_tube_uniform_nnreal_lemma
    (f : ℝ≥0 → ℝ) (R : ℝ)
    (hTube : ∀ u : unitInterval,
      u ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      f ⟨u, u.2.1⟩ ≤ R) :
    ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) → f t ≤ R := by sorry
