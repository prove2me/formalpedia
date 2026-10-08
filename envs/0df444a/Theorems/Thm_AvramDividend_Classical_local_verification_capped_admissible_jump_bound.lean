-- Prove2me | Theorems.Thm_AvramDividend_Classical_local_verification_capped_admissible_jump_bound
-- name    : AvramDividend.Classical.local_verification_capped_admissible_jump_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:23:18.177396+00:00
-- url     : https://prove2.me/theorems/fe854eb3-cb9a-4595-aa64-8db91c9556a6
-- title:
--   Original local-verification HJB controls every right dividend payment for a capped admissible strategy, including cap and time-zero boundaries
-- statement:
--   For a capped admissible dividend strategy D with initial reserve ofReal x≤C, the exact HJB C¹/C² regularity and max-equals-zero conditions of Proposition 4 imply that every right dividend payment before ruin or at time zero is bounded by the verification function's decrease. The reserve may be exactly at the cap. This is the generic, all-boundaries, singular-jump payment inequality required for the classical local verification proof.
-- source:
--   Children admissibleLe_riskProcess_le_cap_all_times, dividendStrategy_le_rightLimit, local_verification_hjb_controls_dividend_jump_le_cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.local_verification_capped_admissible_jump_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) := by sorry
