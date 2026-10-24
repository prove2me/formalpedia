-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_weighted_BCF_full_kernel_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:53:35.15483+00:00
-- url     : https://prove2.me/theorems/5089494b-24db-4cb0-8048-b2f015975ddb
-- title:
--   Continuity of the full weighted causal BCF integral on nonnegative time
-- statement:
--   The causal Volterra convolution of the full kernel β+K with an exponentially weighted bounded continuous input is continuous on the closed nonnegative half-line. Interior continuity comes from the proved L1 convolution continuity theorem; the positive-time limit is zero; the value of the empty integral at zero is zero. A generic right-continuity gluing lemma gives continuity on Ici 0.
-- source:
--   Previously proved positive-time convolution continuity and separately authored weighted origin limit and right continuity glue lemmas.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_causal_full_kernel_continuousOn_positive
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_full_kernel_vanishes_origin
import Theorems.Thm_AvramDividend_Classical_causal_right_continuity_glue
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_full_kernel_continuousOn_nonnegative
    (K : ℝ → ℝ) (β w : ℝ)
    (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
        (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)
      (Ici (0 : ℝ)) := by sorry
