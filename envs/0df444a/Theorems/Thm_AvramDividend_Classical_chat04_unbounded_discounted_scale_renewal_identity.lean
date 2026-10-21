-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_discounted_scale_renewal_identity
-- name    : AvramDividend.Classical.chat04_unbounded_discounted_scale_renewal_identity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T05:03:34.544974+00:00
-- url     : https://prove2.me/theorems/8ad16a6e-b264-4082-b657-03bca074001b
-- title:
--   The discounted q-scale payoff is a renewal identity, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function. Then the discounted q-scale payoff is a renewal identity: the expectation of exp(-q t) W(x + X_t) equals W(x) itself, for every starting point x and every time t. This is the fundamental renewal identity of the scale function, and it is the analytic reason why the discounted q-scale payoff is a martingale: conditioning on the past and using the identity at the later time turns the conditional expectation of the discounted payoff into the current discounted payoff. No standing assumption is required.
-- source:
--   The fundamental renewal identity of the q-scale function of a spectrally negative Levy process. The scale function is the renewal density of the killed process, so the discounted payoff of the killed reserve is a martingale. The Laplace transform of the scale function is the Proved theorem scaleFunction_shifted_laplace_transform, and the independent-increment decomposition is the Proved theorem chat04_scale_random_state_tonelli_semigroup. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_discounted_scale_renewal_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    (∫ ω, Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω) ∂P) =
      W x := by sorry
