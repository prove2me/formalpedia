-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_preruin_postpayment_nonnegative
-- name    : AvramDividend.Classical.avram_p4_e_localise_preruin_postpayment_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:42:15.009648+00:00
-- url     : https://prove2.me/theorems/d6323bfa-a82d-4001-baa9-610d8d3f0f6a
-- title:
--   Original pre-ruin reserve remains nonnegative after the inclusive right dividend payment
-- statement:
--   For the original spectrally negative Levy process, original reserve and admissible cap-constrained dividend strategy, every point before ruin and physical time zero leaves a nonnegative reserve immediately after the right dividend payment. This uses exactly the IsAdmissible rightLimit jump budget and the source riskProcess definition. The proof has no occupation-time, martingale or stochastic-integral assumptions. It supports the nonnegative postpayment endpoint branch at the exact stopped clock.
-- source:
--   Source DividendStrategy: IsAdmissibleLe, IsAdmissible and riskProcess, original Avram Proposition 4(i) before ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_preruin_postpayment_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    0 ≤ x + X.X t ω - rightLimit D t ω := by sorry
