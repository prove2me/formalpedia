-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
-- name    : AvramDividend.Classical.levy_wholePath_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:26:15.316437+00:00
-- url     : https://prove2.me/theorems/840bbf85-6d2b-4b05-a1d1-8712ce085afc
-- title:
--   Whole path of a spectrally negative Lévy process is product-measurable
-- statement:
--   The entire nonnegative-time Lévy process viewed as a function-valued random variable is measurable in the coordinate-product measurable space. Apply the already Proved whole stopped-future-path measurability theorem at the constant zero stopping time and simplify the Lévy increment X(t)-X(0) using the exact field X_zero. This removes a redundant explicit path-measurability premise from subsequent strong Markov grid-event transfers.
-- source:
--   The original SpectrallyNegativeLevy adaptedness and origin normalisation, and Proved finite-stopping-time whole-future-path measurability theorem 722354f7-aca7-470b-8d9d-cf00d3ab29c5.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_wholePath_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) := by sorry
