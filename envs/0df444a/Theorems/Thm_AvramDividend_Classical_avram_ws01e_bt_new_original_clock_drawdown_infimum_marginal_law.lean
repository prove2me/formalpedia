-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T01:23:43.018862+00:00
-- url     : https://prove2.me/theorems/06e38c5b-ec80-4f21-b817-a366230f5179
-- title:
--   Actual original exponential-clock terminal drawdown and centred running-infimum Borel law
-- statement:
--   For an actual original spectrally negative Lévy process under its genuine path law P and independent Exp(p) clock, p>0, the complete pushforward distribution of the actual terminal drawdown S_e−X_e equals the pushforward distribution of X_0−inf_{s≤e}X_s. This is a measurable second-marginal consequence of the already accepted full original-clock affine pair reversal law; it does not assume independent coordinates, skip the finite-clock end point, or replace the centred infimum by a pointwise zero-start form without proof. This marginal-law interface permits any Borel reward, including the Laplace tests needed for descending Wiener–Hopf factors.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_affine_reflected_pair_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_original_clock_drawdown_infimum_marginal_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p) :
    (P.prod (expMeasure p)).map
      (fun z : Ω × ℝ =>
        runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1) =
    (P.prod (expMeasure p)).map
      (fun z : Ω × ℝ =>
        X.X 0 z.1 +
          -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ z.2.toNNReal ∧ y = X.X s z.1}) := by sorry
