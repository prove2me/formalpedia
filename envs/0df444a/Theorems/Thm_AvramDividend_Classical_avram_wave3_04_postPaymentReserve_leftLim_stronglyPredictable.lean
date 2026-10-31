-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:50:00.80553+00:00
-- url     : https://prove2.me/theorems/94ee9994-3882-4f29-8637-06666efe721d
-- title:
--   Original controlled Lévy reserve strict-left-limit process is strongly predictable
-- statement:
--   Under exactly the original spectrally negative Lévy source and actual adapted left-continuous dividend strategy, the process of strict left limits of the càdlàg post-payment reserve x+X_t-D(t+) is strongly predictable relative to the right-continuous filtration constructed from the original source. The proof uses finite left limits, transport-preserved strong adaptedness, left-continuity of left-limit paths and the accepted predictable-process theorem. No equal-law process substitution, additional Brownian/Poisson model or semimartingale identity is assumed.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), source controlled reserve. Accepted Prove2Me dependencies: source finite left-limit bound UUID 490a1c4e-3eeb-490b-815d-c03ef12d0b84; source strongAdapted UUID d1d43051-bc47-49b9-b60f-08a6e9cc7087; generic leftLim strongAdapted 4a78651d-055e-4df8-a3d2-237dd30e6889; leftLim leftContinuous ed804a27-2f90-48f6-ae95-da4acf17e44e; strongAdapted leftContinuous predictable 5ae104c4-13de-429a-a344-76d22511259b. Private compiler probe 4b03d3c7-3771-425d-911e-f58a326cdc5c passed sentinel with source SHA-256 2d33dc0b3fdab0f7026a43e8c31b214e99d2355fe84b0e53ecc99e3656122904.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_prejump_upper
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by sorry
