-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:51:34.766467+00:00
-- url     : https://prove2.me/theorems/1a8d4fdc-8d28-4c8b-bceb-8d436b899ebc
-- title:
--   Actual Esscher random-clock supremum exponential moment in the finite rate gap
-- statement:
--   Under the actual random-terminal Esscher density and the shifted positive root lam, the supremum exponential moment satisfies (lam-beta) E[exp(beta S_e)] = lam in ENNReal form whenever beta<lam. It follows from the independently proved genuine Exp(lam) supremum pushforward law and the proved exponential-clock scalar rate-gap calculation, without any independence assumption on the descending drawdown.
-- source:
--   Kuznetsov–Kyprianou–Rivero (2013), §2.1 exponential supremum Wiener–Hopf factor; Proved source-specific tilted supremum law cf4dc156-a2f9-41cc-85ef-d6492b918ccf; Proved exponential scalar rate-gap moment a63b0a47-ee0a-45f0-8a1e-51dcda707317.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_tilted_supremum_lintegral_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q p lam β : ℝ) (hφ : 0 < φ) (hq : 0 < q)
    (hroot : X.ψ φ = q) (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p) (hβlam : β < lam) :
    ENNReal.ofReal (lam - β) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp (β * runningSup X (Real.toNNReal z.2) z.1))
        ∂((P.prod (ProbabilityTheory.expMeasure p)).withDensity
          (fun z : Ω × ℝ => ENNReal.ofReal
            (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
              (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) =
    ENNReal.ofReal lam := by sorry
