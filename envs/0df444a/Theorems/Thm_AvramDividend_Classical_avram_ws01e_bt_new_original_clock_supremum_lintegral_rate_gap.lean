-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:45:08.924517+00:00
-- url     : https://prove2.me/theorems/a4d6b2d4-a167-444b-bab4-c707f819a8a7
-- title:
--   Actual original exponential-clock supremum positive exponential moment at the root-rate gap
-- statement:
--   For any genuine spectrally negative Lévy process X with positive Laplace root λ satisfying ψ(λ)=p>0, at an actual independent Exp(p) clock the ENNReal integral of exp(β runningSup) for every real β<λ satisfies (λ−β) times the integral equals λ. The proof transports the accepted genuine original-clock supremum pushforward law to Exp(λ), then uses the accepted exact scalar exponential MGF. This does not assert a nonexistent product-tilted process law and requires no β≥0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_true_exp_clock_supremum_full_law_ws01d
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_supremum_lintegral_rate_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p)
    (β : ℝ) (hβlam : β < lam) :
    ENNReal.ofReal (lam - β) *
      (∫⁻ z : Ω × ℝ,
        ENNReal.ofReal (Real.exp
          (β * runningSup X (Real.toNNReal z.2) z.1))
          ∂(P.prod (ProbabilityTheory.expMeasure p))) =
    ENNReal.ofReal lam := by sorry
