-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
-- name    : AvramDividend.Classical.causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:10:51.281297+00:00
-- url     : https://prove2.me/theorems/8896651a-21e2-4bcc-a87f-56ce7c91bffe
-- title:
--   Continuity through time zero of an L1 causal convolution with a locally bounded input
-- statement:
--   If K is L1 on (0,∞) and V is continuous on [0,∞) and bounded on bounded positive intervals, then x↦∫_(0,x]K(x−s)V(s)ds is continuous on all of [0,∞), including x=0. The already-Proved positive-time convolution continuity theorem gives continuity away from zero, while the causal-L1 endpoint-limit theorem gives convergence to the integral's zero value at the origin. Use the general positive-limit gluing theorem to conclude continuity on the closed half-line.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_Ici_of_positive_limit
open AvramDividend.Classical MeasureTheory Set
open scoped Topology

theorem AvramDividend.Classical.causal_l1_convolution_continuousOn_nonnegative_of_locally_bounded
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ici (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C) :
    ContinuousOn (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume)
      (Ici (0 : ℝ)) := by sorry
