-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact
-- name    : AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:09:32.064219+00:00
-- url     : https://prove2.me/theorems/11ad1ad2-0b89-4c20-820c-c6a87c404cdb
-- title:
--   The actual controlled BV Lévy reserve has finite total variation on every compact time interval
-- statement:
--   On a single almost-sure event, the actual reserve x+X-D of every monotone adapted left-continuous admissible dividend strategy has finite total variation on every finite horizon. The dividend control may carry continuous, singular-continuous and right-atomic Stieltjes payment mass. This supplies the source-faithful regulated path-variation prerequisite to a controlled BV Itô–Meyer estimate, without assuming the full stochastic supermartingale conclusion.
-- source:
--   Use the canonically Proved all-times monotone drift-residual theorem f6cc1059 and full-partition controlled-reserve variation bound 2faae607. Uniformly bound every finite monotone-grid variation on [0,T] by dT+(dT-X_T)-(d0-X_0)+(D_T-D_0), then take the supremum defining Mathlib eVariationOn.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_controlled_reserve_boundedVariationOn_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn (fun t : ℝ≥0 => riskProcess X x D t ω) (Icc 0 T) := by sorry
