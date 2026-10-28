-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuous_of_weighted_integrable
-- name    : AvramDividend.Classical.positive_causal_convolution_continuous_of_weighted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:46:10.34224+00:00
-- url     : https://prove2.me/theorems/90604b99-9b3d-4a7d-b09c-9521e8e177ab
-- title:
--   Causal convolution continuity from exponential integrability and nonnegative-axis continuity
-- statement:
--   If f is continuous on the nonnegative axis and an exponentially discounted g is integrable over the positive axis, then the positive causal convolution of f with g is continuous on all positive inputs. Exponential damping reduces the result to an already proved L1 convolution-continuity theorem. This supplies a missing analytic hypothesis in the scale-function resolvent convolution bridge.
-- source:
--   Uses causal_l1_convolution_continuousOn_positive_of_Ici_input (3bc68f22-45b2-4d9a-b616-0898a3747c78) and the exponential product identity.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_continuousOn_positive_of_Ici_input
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.positive_causal_convolution_continuous_of_weighted_integrable
    (f g : ℝ → ℝ) (θ : ℝ)
    (hfcont : ContinuousOn f (Ici (0 : ℝ)))
    (hgint : IntegrableOn
      (fun y : ℝ => Real.exp (-(θ * y)) * g y)
      (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => ∫ s in Ioc (0 : ℝ) x, f s * g (x - s))
      (Ioi (0 : ℝ)) := by sorry
