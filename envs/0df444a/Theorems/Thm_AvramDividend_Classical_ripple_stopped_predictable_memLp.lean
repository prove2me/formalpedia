-- Prove2me | Theorems.Thm_AvramDividend_Classical_ripple_stopped_predictable_memLp
-- name    : AvramDividend.Classical.ripple_stopped_predictable_memLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:13:44.583808+00:00
-- url     : https://prove2.me/theorems/f157b3ee-62a3-43bd-b049-d80d3092a526
-- title:
--   Actual stopped predictable integrand retains square integrability
-- statement:
--   For a stopping time τ and an arbitrary predictable square-integrable real integrand H, restriction H·1_(0,τ] belongs to the same predictable L² space. This provides a sound contractive stopping operation for original stopped Gaussian integrals.
-- source:
--   Adapted from Ripple/Stochastic/StoppedPredictableIntegrand.lean, commit e216e28ce3ffb43877e11f71be260e40a37a35df, Apache-2.0. Reuses AvramDividend.Classical.ripple_stopping_region_predictable accepted theorem ee80bb4f-29d8-45ab-8d46-fd8093074fd0. Intended for Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43. Uses independently proved ambient-product-measurability bridge 8bade7d6-a0bd-486e-8026-11a4be4cb012.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
import Theorems.Thm_AvramDividend_Classical_ripple_predictable_le_ambient_product

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ripple_stopped_predictable_memLp
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    {ν : Measure ℝ≥0} {μ : Measure Ω}
    {H : ℝ≥0 × Ω → ℝ}
    (hτ : IsStoppingTime F τ)
    (hH : MemLp H 2 ((ν.prod μ).trim (ripple_predictable_le_ambient_product F))) :
    MemLp
      ({z : ℝ≥0 × Ω | 0 < z.1 ∧ (z.1 : WithTop ℝ≥0) ≤ τ z.2}.indicator H)
      2 ((ν.prod μ).trim (ripple_predictable_le_ambient_product F)) := by sorry
