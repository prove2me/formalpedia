-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_transport_same_process
-- name    : AvramDividend.Classical.dividendValue_transport_same_process
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:22:07.005969+00:00
-- url     : https://prove2.me/theorems/05a792b8-ac51-49cd-a9c4-8f4e51f2fd97
-- title:
--   Dividend reward is invariant under a filtration change preserving the Lévy sample paths
-- statement:
--   For spectrally negative Lévy structures X on the original filtration and Y on its right-continuous augmentation, assume their sample-path processes agree exactly. Then the full expected discounted dividend value of any fixed control D is identical for both process structures, for arbitrary real q and initial capital x. This follows because the ruin-time infima are built solely from sample paths X_t and D_t, paymentTimes depends only on ruin time, and dividendMeasure depends only on the dividend path. This is an independent deterministic/equational proof needed to transfer an eventual stochastic upper bound back from the augmented filtration to the original model.
-- source:
--   Exact pinned Formalpedia definitions dividendValue, ruinTime, riskProcess, paymentTimes and dividendMeasure.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_transport_same_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕.rightCont)
    (hXY : Y.X = X.X)
    (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    dividendValue Y q x D = dividendValue X q x D := by sorry
