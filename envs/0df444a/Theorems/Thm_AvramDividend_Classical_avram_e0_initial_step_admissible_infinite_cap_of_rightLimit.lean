-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
-- name    : AvramDividend.Classical.avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:07:00.958384+00:00
-- url     : https://prove2.me/theorems/be720d99-17b2-427c-af9b-92e76698f4b9
-- title:
--   An initially bounded lump-sum dividend step is infinitely capped admissible
-- statement:
--   For an original spectrally negative Lévy process, an initial-only dividend strategy with an initial payment bounded by capital and a verified right-limit identity is admissible at infinite cap. The initial jump is affordable; all subsequent jump increments vanish, and strictly pre-ruin reserves are nonnegative.
-- source:
--   Source IsAdmissibleLe, pre-ruin reserve nonnegativity c26c83f7, original target e0b94d7f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_e0_initial_step_admissible_infinite_cap_of_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (K : Ω → ℝ)
    (hstrategy : IsDividendStrategy 𝓕 (fun t ω => if t = 0 then 0 else K ω))
    (hright : ∀ ω (t : ℝ≥0),
      rightLimit (fun s ω => if s = 0 then 0 else K ω) t ω = K ω)
    (hKle : ∀ ω, K ω ≤ x) :
    IsAdmissibleLe X x ⊤ (fun t ω => if t = 0 then 0 else K ω) := by sorry
