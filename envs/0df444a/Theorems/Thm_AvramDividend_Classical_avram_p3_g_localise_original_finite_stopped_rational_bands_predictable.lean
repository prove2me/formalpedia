-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_finite_stopped_rational_bands_predictable
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_finite_stopped_rational_bands_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:41:32.347906+00:00
-- url     : https://prove2.me/theorems/142f2309-3ab2-463e-b58d-2191dde953d3
-- title:
--   Finite original ruin-stopped rational interior band unions are predictable
-- statement:
--   For the original X.X minus rightLimit D pre-reserve and actual finite ruin-truncated clock, every deterministic finite family of rational interior strips with compact enlargement inside 0<U<C yields a predictable finite stopped band union. This is the finite approximant to the separately Proved exact countable rational cover and requires no zero occupation of the cap.
-- source:
--   Direct application of Proved original stopped rational-band predictability 6cb1fc9e and official Mathlib Finset.measurableSet_biUnion.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_admissible_stopped_rational_band_predictable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_finite_stopped_rational_bands_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (S : Finset (ℚ × ℚ))
    (hBands : ∀ ab ∈ S,
      0 < (ab.1 : ℝ) ∧
      Icc ((ab.1 : ℝ) / 2) (ab.2 : ℝ) ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let Z : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    MeasurableSet[𝓕.rightCont.predictable]
      (⋃ ab ∈ S,
        {p : ℝ≥0 × Ω |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Z p ∈ Ioo (ab.1 : ℝ) (ab.2 : ℝ)}) := by sorry
