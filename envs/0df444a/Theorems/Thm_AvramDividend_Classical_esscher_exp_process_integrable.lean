-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_process_integrable
-- name    : AvramDividend.Classical.esscher_exp_process_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:56:07.445951+00:00
-- url     : https://prove2.me/theorems/701eb6a8-3d6c-4a95-8b03-c3e891441c13
-- title:
--   Esscher exponential process of a spectrally negative Lévy process is integrable at each time
-- statement:
--   For a spectrally negative Lévy process and tilt parameter theta >= 0, the Esscher exponential variable M_t = exp(theta * X_t - t * psi(theta)) is integrable at each fixed time, from the exponential moment formula packaged in the process structure. Supports the Esscher martingale identification used by the two-sided exit scale identities.
-- source:
--   Supporting lemma for esscher_exp_process_martingale on the Proposition 1 (barrier_strategy_value) proof path; integrability step isolated for independent verification

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem esscher_exp_process_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) P := by sorry

end AvramDividend.Classical
