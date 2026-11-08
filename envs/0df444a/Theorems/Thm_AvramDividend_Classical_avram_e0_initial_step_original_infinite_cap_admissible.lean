-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_original_infinite_cap_admissible
-- name    : AvramDividend.Classical.avram_e0_initial_step_original_infinite_cap_admissible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T21:38:59.245107+00:00
-- url     : https://prove2.me/theorems/0f4ff6f3-40a9-4469-8989-438fa409bed2
-- title:
--   An initially measurable affordable random dividend mark is source-admissible at infinite cap
-- statement:
--   For any genuine Avram spectrally negative Lévy process, a time-zero measurable nonnegative random dividend amount no greater than initial capital yields a fully original-source IsAdmissibleLe strategy at infinite cap. This supplies the stochastic-control admissibility requirement for the geometric-reserve countermodel.
-- source:
--   Proved e0 rightlimit 7fa270ec, strategy, and conditional admissibility be720d99.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_only_dividend_rightlimit
import Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_step_original_infinite_cap_admissible
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hKnonneg : ∀ ω, 0 ≤ K ω)
    (hKmeas : Measurable[𝓕 0] K)
    (hKle : ∀ ω, K ω ≤ x) :
    IsAdmissibleLe X x ⊤ (fun t ω => if t = 0 then 0 else K ω) := by sorry
