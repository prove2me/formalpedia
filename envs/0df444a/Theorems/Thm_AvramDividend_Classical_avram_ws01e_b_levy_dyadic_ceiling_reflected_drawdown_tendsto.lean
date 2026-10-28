-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto
-- name    : AvramDividend.Classical.avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:06:37.310742+00:00
-- url     : https://prove2.me/theorems/b62d3c82-f0f3-4d86-bc20-a1e35f10b467
-- title:
--   Actual spectrally negative Lévy drawdown converges along every right-ceiling dyadic observation clock
-- statement:
--   For the actual spectrally negative Lévy path X and every sample point ω and nonnegative time t, the reflected drawdown runningSup(X,r_n)-X(r_n) at the dyadic ceiling time r_n=ceil(2^n t)/2^n converges to the genuine drawdown at t. There is no exceptional-null-set caveat, because the Lévy structure assumes pathwise right continuity and the Proved running supremum right-continuity theorem applies at every ω,t. This directly verifies the genuine-path limiting step of the product-Pi-measurable dyadic ceiling reward approximants used to turn the uncapped random-terminal Esscher upper-record full-path regeneration f5788ba0 into Wiener–Hopf supremum/drawdown independence. Import the Proved dyadic ceiling time convergence, time ≥t and actual running-supremum right continuity; take limits through the difference of the two right-continuous paths.
-- source:
--   Source-specific first-record drawdown reconstruction in Avram WS1E-B. Uses Proved 9faeaaa4-6933-425a-ac6d-88d7bf48aa56, 5c6df1d9-08d7-4a57-b3fc-94f32588e34b, c2451a3a-6c5f-45bc-ba0f-ea173787bf91.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_right_continuous_actual
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_levy_dyadic_ceiling_reflected_drawdown_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let r : ℝ≥0 := (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n
      runningSup X r ω - X.X r ω)
      atTop (𝓝 (runningSup X t ω - X.X t ω)) := by sorry
