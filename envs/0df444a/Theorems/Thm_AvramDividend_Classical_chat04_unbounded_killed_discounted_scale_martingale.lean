-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_discounted_scale_martingale
-- name    : AvramDividend.Classical.chat04_unbounded_killed_discounted_scale_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T08:43:05.211999+00:00
-- url     : https://prove2.me/theorems/5cce898d-6355-4a98-961a-0e1c0aa14b60
-- title:
--   The discounted q-scale payoff of the killed reserve is a martingale, for unbounded-variation processes and without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation, let q > 0, and let W be its q-scale function, which vanishes on the negative half-line. Start the reserve at x and kill the process at the first time the reserve falls below zero. The discounted q-scale payoff of the killed reserve, extended by zero past the killing time, is a martingale with respect to the natural filtration of X. The survival condition in the integrand is essential and is a condition on the whole path up to t, not only on the terminal value: the payoff is the one of the killed process, not of the raw process, which may cross below zero and come back. This is the without-standing counterpart of the martingale for the standing case; it holds for the unbounded-variation case because the q-harmonicity of the scale function is then available without the standing integrability of the process increment.
-- source:
--   The martingale property of the killed q-scale payoff, the analytic ingredient of the optional-stopping proof of the two-sided exit identity for a spectrally negative Levy process. The survival condition is the same pathwise event as in the Proved theorem chat04_three_grid_survival_scale_tonelli and in the Proved theorem chat04_unbounded_closed_horizon_killed_scale_grid_limit. The standing counterpart is the Proved theorem chat04_killed_discounted_scale_martingale. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_discounted_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) :
    Martingale
      (fun t ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω)
      𝓕 P := by sorry
