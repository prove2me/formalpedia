-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_input_primitive_continuousOn_nonnegative
-- name    : AvramDividend.Classical.causal_continuous_input_primitive_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:10:59.385625+00:00
-- url     : https://prove2.me/theorems/6ca14f46-2c96-40aa-a8d9-037a2a7d0556
-- title:
--   Continuity of the nonnegative-time primitive of a continuous input
-- statement:
--   If V is continuous on [0,∞), its causal primitive x↦∫_(0,x]V(s)ds is continuous on [0,∞), without requiring global integrability or boundedness. Compose V with max(x,0) to obtain a continuous full-real-line extension, apply Mathlib's continuous_primitive theorem, and identify the resulting oriented integral with the causal set integral for x≥0. The lemma handles the constant β drift part of a full Volterra convolution operator.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousOn
open MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_continuous_input_primitive_continuousOn_nonnegative
    (V : ℝ → ℝ)
    (hV : ContinuousOn V (Ici (0 : ℝ))) :
    ContinuousOn (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, V s ∂volume)
      (Ici (0 : ℝ)) := by sorry
