-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_continuous_positive
-- name    : AvramDividend.Classical.causal_weighted_kernel_continuous_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:31:50.56318+00:00
-- url     : https://prove2.me/theorems/5161d6f1-1e9b-4583-933a-9d5034eb79d2
-- title:
--   Exponential damping preserves continuity of a causal drift-plus-kernel on positive times
-- statement:
--   A kernel continuous on the positive half-line remains continuous there after adding a real constant and multiplying by a real exponential damping factor. This is the continuity input for termwise differentiation of the exponentially weighted causal Volterra Neumann resolvent.
-- source:
--   Elementary continuity bridge in the Gaussian Lévy double-tail C2 regularity programme; no continuity at zero is assumed.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Basic

open Set

theorem AvramDividend.Classical.causal_weighted_kernel_continuous_positive
    (K : ℝ → ℝ) (w β : ℝ)
    (hK : ContinuousOn K (Ioi (0 : ℝ))) :
    ContinuousOn (fun t : ℝ => Real.exp (-w * t) * (β + K t))
      (Ioi (0 : ℝ)) := by sorry
