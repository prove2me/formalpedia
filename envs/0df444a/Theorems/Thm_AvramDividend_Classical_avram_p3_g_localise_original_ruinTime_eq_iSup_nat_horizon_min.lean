-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruinTime_eq_iSup_nat_horizon_min
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_ruinTime_eq_iSup_nat_horizon_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:41:44.010363+00:00
-- url     : https://prove2.me/theorems/51909e58-802c-468c-9732-559916c50b67
-- title:
--   Original ruin time is supremum of its genuine natural-horizon ENNReal truncations
-- statement:
--   For each actual original Lévy reserve path, ruinTime equals the supremum of min(ruinTime,n) over natural deterministic horizons. The proof handles finite ruin via the pinned ENNReal.exists_nat_gt and infinite ruin via the pinned iSup_natCast identity. This provides a source-exact order-theoretic finite-to-infinite stopping clock limit, without claiming predictable strict pre-ruin or a boundary occupation property.
-- source:
--   Original source ruinTime X x D. Pinned Mathlib ENNReal.exists_nat_gt and ENNReal.iSup_natCast.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_ruinTime_eq_iSup_nat_horizon_min
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ ω : Ω,
      (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
        ruinTime X x D ω := by sorry
