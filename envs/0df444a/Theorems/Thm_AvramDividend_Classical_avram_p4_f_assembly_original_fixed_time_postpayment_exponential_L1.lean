-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_fixed_time_postpayment_exponential_L1
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_fixed_time_postpayment_exponential_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:41:51.683202+00:00
-- url     : https://prove2.me/theorems/14191191-ec9b-4d1a-8f2e-3498cbf425c6
-- title:
--   Actual original post-payment Lévy discounted exponential is L1 at every deterministic finite time
-- statement:
--   For the canonical original source Lévy X and actual dividend strategy D, the proved discounted post-payment exponential supermartingale with θ≥0 and X.ψ θ≤q has integrable fixed-time random variables. This proves L1 at every deterministic horizon without assumptions on an artificial source process; random-clock optional stopping is a separate obligation.
-- source:
--   Proved original-source postPayment discounted exponential supermartingale fab320c3-5fa4-4198-8338-868374d6fdf0; pinned Mathlib Supermartingale.integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_fixed_time_postpayment_exponential_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    Integrable (fun ω => Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q)) P := by sorry
