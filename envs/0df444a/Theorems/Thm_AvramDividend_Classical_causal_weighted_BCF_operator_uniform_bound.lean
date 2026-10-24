-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_operator_uniform_bound
-- name    : AvramDividend.Classical.causal_weighted_BCF_operator_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:16:47.320256+00:00
-- url     : https://prove2.me/theorems/c980086c-7930-4b08-8442-fcc097acde63
-- title:
--   Uniform BCF norm control for a weighted causal Volterra operator
-- statement:
--   Under the same strict weighted-mass assumption as the resolvent theorem, the causal convolution applied to the exponentially unweighted bounded-continuous function f has weighted modulus at most m ||f|| with a nonnegative m<a independent of f and the time horizon. Combine the proven strict operator estimate with continuity and local boundedness of the reweighted extension, then bound its weighted finite-horizon supremum by the BCF norm. This is the central operator inequality for constructing an affine contraction.
-- source:
--   Combines four targeted Prove2Me helper statements that isolate kernel mass, input regularity, local bounds and pointwise weighted norm cancellation.

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Theorems.Thm_AvramDividend_Classical_causal_weighted_volterra_strict_operator_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_extension_continuous
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_local_bound
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_pointwise_norm_bound
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_weighted_BCF_operator_uniform_bound
    (K : ℝ → ℝ) (f : BoundedContinuousFunction ℝ≥0 ℝ)
    (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    ∃ m : ℝ, 0 ≤ m ∧ m < a ∧
      ∀ (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R),
        Real.exp (-(w * x)) *
          |∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume| ≤
          ‖f‖ * m := by sorry
