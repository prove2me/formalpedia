-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftApprox_strongMeasurable
-- name    : AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftApprox_strongMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T10:09:19.784816+00:00
-- url     : https://prove2.me/theorems/173f3c78-6fda-4deb-bd5b-174287d0bcfd
-- title:
--   Countable past-time approximation to the genuine controlled Lévy reserve has strongly measurable limit
-- statement:
--   At any fixed time t and for the original spectrally negative Lévy process with admissible source-form dividend strategy, the limit-under of the countable strictly-past sequence of post-payment reserves U+(t−t/(n+2)) is strongly measurable with respect to the enlarged information at t. Each approximating time is ≤t, so adaptedness and filtration monotonicity make each section measurable at t; Mathlib's strongly measurable limit theorem gives the claim. For positive t, this is the natural left-approximation to the reserve, although identifying its limit with the actual left limit is a separate required pathwise result. The theorem introduces no stochastic integration hypothesis.
-- source:
--   Pinned Mathlib `MeasureTheory.StronglyMeasurable.limUnder` from Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable, together with canonical Proved postPaymentReserve_cadlag_adapted UUID a2763475-d54e-4660-aa60-6ec74b85deb7. Uses a countable time sequence to satisfy the theorem's countability condition, which fails on a direct ℝ≥0-indexed neighbourhood filter.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_postPaymentReserve_leftApprox_strongMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) :
    StronglyMeasurable[𝓕.rightCont t]
      (fun ω => Filter.limUnder atTop
        (fun n : ℕ =>
          x + X.X (t - t / ((n : ℝ≥0) + 2)) ω -
            rightLimit D (t - t / ((n : ℝ≥0) + 2)) ω)) := by sorry
