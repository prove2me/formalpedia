-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_process_martingale
-- name    : AvramDividend.Classical.esscher_exp_process_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:46:16.863739+00:00
-- url     : https://prove2.me/theorems/2011c7d7-83f6-4777-a61f-f89d06c7aeda
-- title:
--   Esscher exponential process of a spectrally negative Lévy process is a martingale
-- statement:
--   Let X be a spectrally negative Lévy process with Laplace exponent psi. For every tilt parameter theta >= 0, the Esscher exponential process M_t = exp(theta * X_t - psi(theta) * t) is a martingale with respect to the underlying filtration. This is the standard change-of-measure engine behind the two-sided exit identities: stopping this martingale at first passage and changing measure yields the scale-function exit formulae. It follows from independent stationary increments (for the conditional property) and the exponential moment formula (for integrability and the drift identification), all packaged in the SpectrallyNegativeLevy structure.
-- source:
--   Standard Lévy fluctuation theory (Kyprianou, Fluctuations of Lévy Processes, Esscher transform); needed by the stopped two-sided exit scale identities two_sided_exit_stopped_scale_identity and chat04_unbounded_two_sided_exit_stopped_scale_identity on the Proposition 1 (barrier_strategy_value) proof path

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem esscher_exp_process_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    Martingale
      (fun (t : ℝ≥0) (ω : Ω) =>
        Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      𝓕 P := by sorry

end AvramDividend.Classical
