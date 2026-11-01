-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
-- name    : AvramDividend.Classical.avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:18:20.480269+00:00
-- url     : https://prove2.me/theorems/6a148bb3-94f4-4dd7-a25f-529d729c3cd5
-- title:
--   Reflected drawdown killing never raises the genuine strict first-record discounted Laplace mass
-- statement:
--   For every positive q, every positive Laplace root φ of the original Lévy exponent, any real reflected drawdown barrier a, and every positive strict upward record height b, the actual discount paid only if the record precedes reflected ruin is bounded by exp(-φb), the unrestricted finite strict first-passage Laplace transform. This is a genuine source-process pathwise event inclusion with an ENNReal lintegral inequality; no Standing, infinite-variation, scale regularity or excursion substitution appears.
-- source:
--   Proved original strict upcrossing Laplace transform 0da3763f-17e2-414b-ac46-9b9f2088aa29 and exact native reflected ruin clock. Pointwise inclusion T_b<D_a implies T_b<∞.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_exact_strict_upcrossing_discount

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_01_reflected_record_discount_le_unrestricted_upcrossing_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∀ a b : ℝ, 0 < b →
      (∫⁻ ω, if twoSidedExitUpTime X b ω <
                    barrierRuinTime X a ω then
          ENNReal.ofReal
            (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
        else 0 ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * b))) := by sorry
