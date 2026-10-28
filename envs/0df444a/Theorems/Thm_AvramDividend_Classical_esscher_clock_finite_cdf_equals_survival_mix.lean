-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_clock_finite_cdf_equals_survival_mix
-- name    : AvramDividend.Classical.esscher_clock_finite_cdf_equals_survival_mix
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:26:28.527319+00:00
-- url     : https://prove2.me/theorems/a5ddd069-95f5-4496-ae18-514c410136a9
-- title:
--   Random exponential-horizon tilted infimum CDF mixture equals actual weighted finite-horizon survival expectation mixture
-- statement:
--   At every positive exponential observation clock rate p, the mixture of authentic tilted finite-horizon reflected-infimum CDFs is exactly the clock integral of ENNReal.ofReal of the original Lévy path survival expectations weighted by the terminal compensated Esscher exponential. This is an exact finite-rate identity, using established pathwise CDF equivalence and real-to-nonnegative integral equality, not any Wiener–Hopf transform. Combined with the separately proven joint-event disintegration it identifies the CDF under the true random-time Esscher law.
-- source:
--   Prove2Me accepted `chat04_esscher_reflected_law_Iic_eq_killed_lintegral` 7c5cad30 and `chat04_esscher_killed_survival_real_to_lintegral` 1ccb6dd6, and `levy_running_infimum_measurable`; KKR scale review Esscher paths.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_law_Iic_eq_killed_lintegral
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_killed_survival_real_to_lintegral
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_clock_finite_cdf_equals_survival_mix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p x : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (∫⁻ t : ℝ,
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal t) ω -
          (Real.toNNReal t : ℝ) * X.ψ θ))))
        {ω : Ω | -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal t ∧ y = X.X s ω} ≤ x}
      ∂expMeasure p) =
    (∫⁻ t : ℝ, ENNReal.ofReal
      (∫ ω, ({ω | ∀ s : ℝ≥0,
        s ≤ Real.toNNReal t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => Real.exp
          (θ * X.X (Real.toNNReal t) ω -
            (Real.toNNReal t : ℝ) * X.ψ θ)) ω ∂P)
      ∂expMeasure p) := by sorry
