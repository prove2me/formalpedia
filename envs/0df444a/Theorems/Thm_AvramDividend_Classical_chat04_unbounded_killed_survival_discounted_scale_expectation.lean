-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_survival_discounted_scale_expectation
-- name    : AvramDividend.Classical.chat04_unbounded_killed_survival_discounted_scale_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T07:05:50.344385+00:00
-- url     : https://prove2.me/theorems/a885f0b3-3960-424d-97e4-abbcffe268ba
-- title:
--   The discounted q-scale payoff of the killed reserve is a renewal identity, with the survival condition, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, q > 0, and W its q-scale function, which vanishes on the negative half-line. Start the reserve at x and kill the process at the first time the reserve falls below zero. The expected discounted killed q-scale payoff at time t is exactly W(x), the scale value at the starting point, independently of t. This is the renewal identity of the killed process, and it is the analytic reason why the killed discounted q-scale payoff is a martingale, which is what the two-sided exit identity uses. The survival condition in the integrand is essential and is a condition on the whole path up to t, not only on the terminal value: the payoff is the one of the killed process, not of the raw process, which may cross below zero and come back. No standing assumption is required.
-- source:
--   The renewal identity of the q-scale function of a spectrally negative Levy process, in the form in which the scale function is the renewal density of the process killed at zero. The survival condition is the same pathwise event as in the Proved theorem chat04_three_grid_survival_scale_tonelli and in the Proved theorem chat04_unbounded_closed_horizon_killed_scale_grid_limit, and the Laplace transform of the scale function is the Proved theorem scaleFunction_shifted_laplace_transform. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_survival_discounted_scale_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by sorry
