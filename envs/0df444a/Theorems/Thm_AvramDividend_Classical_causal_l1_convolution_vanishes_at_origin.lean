-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
-- name    : AvramDividend.Classical.causal_l1_convolution_vanishes_at_origin
-- status  : Open
-- author  : @WillR
-- created : 2026-10-22T23:28:22.817992+00:00
-- url     : https://prove2.me/theorems/8dc48bbf-1373-4994-8364-e2cc350b1375
-- title:
--   Causal convolution with L1 kernel vanishes at time zero
-- statement:
--   If K is L1 on positive times and V is continuous and locally bounded there, its causal convolution ∫₀ˣ K(x−s)V(s)ds converges to zero as x↓0. The finite-horizon norm is bounded by a fixed local supremum of V times the kernel mass ∫₀ˣ|K(s)|ds, and this mass tends to zero by the proved L1-primitive continuity lemma. This proves endpoint continuity of the Volterra fixed-point operator.

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_primitive_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_abs_le_finite_mass
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_convolution_vanishes_at_origin
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    Tendsto (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x,
      K (x - s) * V s ∂volume)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (nhds 0) := by sorry
