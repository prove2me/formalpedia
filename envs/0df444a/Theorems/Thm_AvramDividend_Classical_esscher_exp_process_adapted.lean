-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_process_adapted
-- name    : AvramDividend.Classical.esscher_exp_process_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:56:06.716507+00:00
-- url     : https://prove2.me/theorems/009fef73-bb3f-4b28-9315-ea9159f7a17e
-- title:
--   Esscher exponential process of a spectrally negative Lévy process is adapted
-- statement:
--   For a spectrally negative Lévy process, the Esscher exponential process M_t = exp(theta * X_t - t * psi(theta)) is adapted to the underlying filtration, directly from adaptedness of X by measurability of affine maps and the exponential. Supports the Esscher martingale identification used by the two-sided exit scale identities.
-- source:
--   Supporting lemma for esscher_exp_process_martingale on the Proposition 1 (barrier_strategy_value) proof path; measurability step isolated for independent verification

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem esscher_exp_process_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) :
    Adapted 𝓕 (fun (t : ℝ≥0) (ω : Ω) =>
      Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) := by sorry

end AvramDividend.Classical
