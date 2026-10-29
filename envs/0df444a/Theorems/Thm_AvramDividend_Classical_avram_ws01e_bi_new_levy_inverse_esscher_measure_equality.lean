-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_levy_inverse_esscher_measure_equality
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_levy_inverse_esscher_measure_equality
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:38:27.123989+00:00
-- url     : https://prove2.me/theorems/605987ac-0429-4d6c-8a33-4add1d804635
-- title:
--   Actual Lévy random-terminal inverse Esscher density identifies the full joint original-clock law
-- statement:
--   For the true spectrally negative Lévy path X and a parameter φ with ψ(φ)=q≥0, reweighting genuine Qp by exp(-φ X_e) and scaling by p+q yields p times exactly P×Exp(p+q), as an equality of measures on the full path-clock product. No independent-clock assumption under Qp is used.
-- source:
--   Immediate actual-source specialisation of genuine toNNReal age measure identity b1078a01, after proving the realised-terminal path is jointly measurable by accepted d55462c3 and substituting ψφ=q. This statement is staged and must not be publicly authored until b1078a01 is canonically Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_inverse_clock_measure_equality

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_levy_inverse_esscher_measure_equality
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p : ℝ) (hq : 0 ≤ q)
    (hroot : X.ψ φ = q) (hp : 0 < p) :
    ENNReal.ofReal (p + q) •
      (((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ)))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (-φ * X.X (Real.toNNReal z.2) z.1)))) =
    ENNReal.ofReal p • (P.prod (expMeasure (p + q))) := by sorry
