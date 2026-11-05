-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_positive_reserve_integrable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_positive_reserve_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:15:51.745168+00:00
-- url     : https://prove2.me/theorems/9fcf5414-c172-4bd7-8dee-4408fc7ed4f0
-- title:
--   Original controlled-dividend ruin-truncated Lévy reserve positive part is integrable from source exponential moment
-- statement:
--   At the exact original finite clock τ=min(ruinTime,n), the positive part of the raw same-process capital x+X_τ is L1, even if X has nonintegrable negative jumps. Use the Proved genuine original stopped Esscher exponential moment at θ=1,q=0, scale by exp(x), and dominate max(x+X_τ,0) by exp(x+X_τ). This is the unbounded-variation cash-terminal comparison input for the cap-linear V and explicitly requires stopped-source measurability.
-- source:
--   Proved source original ruin-clock exponential L1 51ec0583-746d-46ed-9584-8dd54835c9e0 and elementary Real.add_one_le_exp; pinned Mathlib Integrable.mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ruin_clock_discounted_exp_integrable_any_q

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_raw_positive_reserve_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hXstopped : Measurable (fun ω => X.X (τ ω) ω)) :
    Integrable (fun ω => max (x + X.X (τ ω) ω) 0) P := by sorry
