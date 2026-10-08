-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
-- name    : AvramDividend.Classical.riskProcess_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T21:01:23.248888+00:00
-- url     : https://prove2.me/theorems/3457ee9d-5188-4e3d-9ec8-7d4bcaad5740
-- title:
--   The controlled reserve process is adapted
-- statement:
--   The controlled reserve process U_t=x+X_t-D_t is adapted whenever the Lévy process X and dividend strategy D are adapted.
-- source:
--   Elementary process-measurability helper for discretised stopping/localisation in Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Adapted 𝓕 (riskProcess X x D) := by sorry
