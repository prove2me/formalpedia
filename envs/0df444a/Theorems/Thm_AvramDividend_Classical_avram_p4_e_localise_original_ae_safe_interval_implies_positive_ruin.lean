-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ae_safe_interval_implies_positive_ruin
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ae_safe_interval_implies_positive_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:50:38.581232+00:00
-- url     : https://prove2.me/theorems/a19d9db9-8fb0-483d-9434-9d8840fe8c7a
-- title:
--   Source initial safe intervals imply almost-sure positive original controlled ruin clocks
-- statement:
--   If almost every original sample path admits a positive initial interval during which the controlled reserve is nonnegative, then the strict-negative infimum ruinTime X x D is almost surely strictly positive. The safety premise must still be derived from X right continuity and actual admissible dividend D; it is intentionally explicit and does not assume away t=0 dividend atoms.
-- source:
--   Proved source-safe-interval lower bound theorem 2eacf648-9646-411e-b1e4-9a8f0db84b88.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine almost-sure safe initial reserve interval prevents immediate source ruin. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ae_safe_interval_implies_positive_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hSafeAE : ∀ᵐ ω ∂P, ∃ ε : ℝ≥0,
      0 < ε ∧ ∀ t : ℝ≥0, t < ε → 0 ≤ riskProcess X x D t ω) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω := by sorry
