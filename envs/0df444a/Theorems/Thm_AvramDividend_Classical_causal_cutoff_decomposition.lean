-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_cutoff_decomposition
-- name    : AvramDividend.Classical.causal_cutoff_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:48:39.679537+00:00
-- url     : https://prove2.me/theorems/23522762-fe12-46e2-8ff2-1a4232d1e276
-- title:
--   Causal L1 kernel splits into continuous bounded tail and short-support remainder
-- statement:
--   A real integrable kernel that is continuous and uniformly bounded away from the origin can be separated, using a ramp cutoff, into a globally continuous bounded tail and an integrable remainder vanishing above twice any chosen positive cutoff. This provides the local regularity decomposition needed to prove continuity of the causal convolution of two such kernels.
-- source:
--   Exact theorem extracted from the first declaration in candidates/chat04_positive_causal_conv_20261023.lean, needed as a source-faithful predecessor of the Open AvramDividend.Classical.continuousOn_positive_causal_convolution_of_locally_bounded_integrable (c039e3d8-3d03-4f1a-85f9-c4de9e3b5260), itself on the BV Esscher renewal-density route to positive-barrier smooth fit.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_cutoff_decomposition
    (f : ℝ → ℝ) (hfint : Integrable f volume)
    (hfcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hfbound : ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |f x| ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F U : ℝ → ℝ, (∀ t, f t = F t + U t) ∧ Continuous F ∧
      BddAbove (range fun t : ℝ => ‖F t‖) ∧ Integrable U volume ∧
      (∀ t, 2 * ε < t → U t = 0) := by sorry
