-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_leftshift_compensated_fixed_terminal_integrable
-- name    : AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:18:24.126124+00:00
-- url     : https://prove2.me/theorems/6b468bb8-f3bb-4da3-9298-9d75b5f45cbe
-- title:
--   Every compensated negative Esscher reward is integrable under any later finite-horizon Esscher law
-- statement:
--   For nonnegative Esscher tilt θ and ε between zero and θ, the compensated negative exponential at an earlier time s is genuinely integrable under the later-horizon Esscher probability law Q_T for every s≤T. This is needed to turn the proved fixed-terminal Esscher earlier-event martingale identity into an actual Mathlib discrete-time martingale on any finite grid, enabling Doob's maximal inequality and a downward-running-infimum bound.
-- source:
--   Integrability under Q_s follows from the accepted finite Esscher negative-exponential integrability and multiplying by a deterministic finite exponential compensation factor. The accepted adaptedness of the compensated process makes the early reward F_s-measurable. Then transfer integrability from Q_s to Q_T using the generic ambient-measure subσ-integrability equivalence and the accepted consistency of Esscher laws on F_s.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_integrable_iff_of_ambient_measures_agree_on_subsigma
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_compensated_leftshift_reward_strongly_adapted
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_leftshift_compensated_fixed_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T) :
    Integrable (fun ω : Ω => Real.exp
      (-ε * X.X s ω -
        (s : ℝ) * (X.ψ (θ - ε) - X.ψ θ)))
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by sorry
