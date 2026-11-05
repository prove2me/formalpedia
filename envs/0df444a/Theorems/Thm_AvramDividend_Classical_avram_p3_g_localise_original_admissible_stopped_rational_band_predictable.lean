-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_rational_band_predictable
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_rational_band_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:24:37.990114+00:00
-- url     : https://prove2.me/theorems/6cb1fc9e-fe05-4475-a563-76bccb787b18
-- title:
--   Original admissible finite ruin-stopped rational interior bands are predictable
-- statement:
--   For the true original ruin-truncated stopping time and actual x+X.X-rightLimit D pre-reserve left limit, any strictly interior open rational band Ioo a b whose enlarged compact interval Icc(a/2)b lies within 0<reserve<C has a right-continuous predictable stopped membership set. The stopped mask includes the stopping instant and is constructed from source admissibility, not a surrogate X, without assuming BV cap or zero occupation vanishes.
-- source:
--   Composes accepted P3-G predictable stopped source boundary regime 6fb43911, accepted physical open-band predictability 913dc24c (pending proof at authoring), and genuine compact strip inclusion.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_interior_zero_cap_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_open_prestate_band_predictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_admissible_stopped_rational_band_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a)
    (hBand : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      {p | (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
        Z p ∈ Ioo a b} := by sorry
