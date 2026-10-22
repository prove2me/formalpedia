-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_scale_martingale
-- name    : AvramDividend.Classical.chat04_killed_discounted_scale_martingale
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T07:59:05.338018+00:00
-- url     : https://prove2.me/theorems/af5ba483-8cb2-4d6d-9711-da17e88f4dc5
-- title:
--   The discounted q-scale payoff of the killed reserve is a martingale, for processes with the standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process with the standing assumptions, let q > 0, and let W be its q-scale function, which vanishes on the negative half-line. Start the reserve at x and kill the process at the first time the reserve falls below zero. The discounted q-scale payoff of the killed reserve, extended by zero past the killing time, is a martingale with respect to the natural filtration of X. The survival condition in the integrand is essential and is a condition on the whole path up to t, not only on the terminal value: the payoff is the one of the killed process, not of the raw process, which may cross below zero and come back. The payoff is extended by zero on the paths that have already been killed, which is written with the set indicator of the survival event. With the survival condition the statement is correct; the version without it, which asserts that the raw discounted payoff is a martingale, is false.
-- source:
--   The standard martingale property of the killed q-scale payoff, as used in the optional-stopping proof of the two-sided exit identity of a spectrally negative Levy process, equation (3.6) of Avram, Palmowski and Pistorius (2007). The survival condition is the same pathwise event as in the Proved theorem chat04_three_grid_survival_scale_tonelli and in the Proved theorem chat04_unbounded_closed_horizon_killed_scale_grid_limit. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_killed_discounted_scale_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) :
    Martingale
      (fun t ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω)
      𝓕 P := by sorry
