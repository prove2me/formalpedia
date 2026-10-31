-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:53:13.051331+00:00
-- url     : https://prove2.me/theorems/d1d43051-bc47-49b9-b60f-08a6e9cc7087
-- title:
--   Genuine post-payment controlled Lévy reserve is strongly adapted after right-continuous filtration transport
-- statement:
--   For the genuinely controlled post-payment reserve U+_t=x+X_t-D(t+), under any original spectrally negative Lévy law and left-continuous adapted increasing dividend strategy, every time section is strongly measurable with respect to the corresponding right-continuous filtration. This upgrades the existing source-correct Adapted property to StronglyAdapted for the original same-path controlled process and is a prerequisite for predictable left-limit integrands. It does not provide a semimartingale chain rule.
-- source:
--   Deduction from canonical Proved postPaymentReserve_cadlag_adapted UUID a2763475-d54e-4660-aa60-6ec74b85deb7, whose original-law and filtration transport hypotheses are preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_stronglyAdapted_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    StronglyAdapted 𝓕.rightCont
      (fun t ω => x + X.X t ω - rightLimit D t ω) := by sorry
