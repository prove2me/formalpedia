-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_finite_reciprocal_grid_integrable_measurable_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_grid_integrable_measurable_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:26:12.458587+00:00
-- url     : https://prove2.me/theorems/c2714cb8-b469-45e4-a91f-a865792ec899
-- title:
--   Original same-X finite negative reciprocal mark count grid measurable and integrable
-- statement:
--   True original-X physical compensated finite reciprocal negative marked count grid measurability and integrability, with exact accepted source and public raw count measurability and original ν Campbell theorem. Necessary for actual signed-mark L1 proxy error.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_count_raw_measurable
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_reciprocal_band_count_L1_Campbell_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_finite_reciprocal_grid_integrable_measurable_20261122
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.Ico n m,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    Measurable S ∧ Integrable S P := by sorry
