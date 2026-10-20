-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_fixed_inverse_nat_grid_exit_measurable
-- name    : AvramDividend.Classical.chat03_fixed_inverse_nat_grid_exit_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:47:41.619341+00:00
-- url     : https://prove2.me/theorems/d28afffa-123b-4e9a-ab63-a69dadb1c107
-- title:
--   Measurability of strict Lévy exits at each deterministic inverse-natural grid time
-- statement:
--   For an adapted official spectrally negative Lévy process and any nonnegative inverse-natural grid time k/n, the event that the observed process is strictly below a lower real threshold or strictly above an upper real threshold is measurable in the ambient sigma algebra. This supplies the deterministic-time components needed to establish measurability of strict continuous-time passage via countable grid approximations.
-- source:
--   Directly from official SpectrallyNegativeLevy adaptedness and filtration inclusion, and pinned Mathlib measurable strict inequalities and unions.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_fixed_inverse_nat_grid_exit_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (n k : ℕ) :
    MeasurableSet
      {ω : Ω |
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by sorry
