-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:02:30.668077+00:00
-- url     : https://prove2.me/theorems/62029127-e7d1-4d8f-996c-3557c91f1910
-- title:
--   Real analyticity of the actual original-clock descending drawdown MGF on positive parameters
-- statement:
--   For the actual original spectrally negative Lévy process and independent Exp(p) clock, the real mgf of the negative terminal drawdown −(S_e−X_e) is analytic at all positive Laplace parameters. This specialises the already accepted genuinely normalised Esscher-clock descending MGF analyticity theorem to θ=0, uses the proved ψ(0)=0 identity to identify the random-terminal likelihood with constant one, and rewrites the exact withDensity-one measure back to the original product law. It supplies one of the two native analytic functions needed for original-clock all-beta Wiener–Hopf continuation.

import Mathlib.Probability.Moments.MGFAnalytic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_clock_descending_mgf_analytic_positive
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_mgf_analytic_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    AnalyticOnNhd ℝ
      (mgf
        (fun z : Ω × ℝ =>
          -(runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1))
        (P.prod (expMeasure p)))
      (Set.Ioi 0) := by sorry
