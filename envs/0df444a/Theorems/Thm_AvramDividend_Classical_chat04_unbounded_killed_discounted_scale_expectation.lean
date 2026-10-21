-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_discounted_scale_expectation
-- name    : AvramDividend.Classical.chat04_unbounded_killed_discounted_scale_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T05:12:20.982265+00:00
-- url     : https://prove2.me/theorems/ff848d0a-2aba-4a17-83c5-375f14acb3f6
-- title:
--   The discounted q-scale payoff of the killed reserve is a renewal identity, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function, which vanishes on the negative half-line. Start the reserve at x, kill the process when the reserve first falls below zero, and discount the killed q-scale payoff at rate q. Then the expected discounted killed payoff at time t is exactly W(x), the scale value at the starting point. This is the renewal identity of the killed process, and it is the analytic reason why the killed q-scale payoff is a martingale, which is what the two-sided exit identity uses. The survival condition in the integrand is essential: the payoff is the one of the killed process, not of the raw process, which may cross below zero and come back. No standing assumption is required.
-- source:
--   The renewal identity of the q-scale function of a spectrally negative Levy process, in the form in which the scale function is the renewal density of the process killed at zero. The Laplace transform of the scale function is the Proved theorem scaleFunction_shifted_laplace_transform, and the independent-increment decomposition with the survival condition is the Proved theorem chat04_three_grid_survival_scale_tonelli. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_discounted_scale_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      if 0 ≤ x + X.X t ω then
        ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else 0 ∂P) =
      ENNReal.ofReal (W x) := by sorry
