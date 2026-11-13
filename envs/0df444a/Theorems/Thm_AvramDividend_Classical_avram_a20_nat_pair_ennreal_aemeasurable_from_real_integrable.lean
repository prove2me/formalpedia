-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
-- name    : AvramDividend.Classical.avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:33:07.033248+00:00
-- url     : https://prove2.me/theorems/68fff94d-6990-48dd-aa07-3be943e67e98
-- title:
--   Integrable doubled natural chronological pair count is almost-everywhere measurable as an ENNReal-valued count
-- statement:
--   For any natural-number-valued random event pair count K on any measure space, if the real function 2K is integrable, then its ENNReal embedding is almost everywhere measurable. Multiply by one half to deduce real K integrability, take the induced a.e. real measurability, compose with measurable ENNReal.ofReal, and use the exact natural-cast identity. This isolates the final measurability bridge required for the genuine original arbitrary-Borel chronological pair moment and its ENNReal-to-real conversion without assuming a sample-space Poisson distribution.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_nat_pair_ennreal_aemeasurable_from_real_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Ω → ℕ)
    (hI : Integrable (fun ω => 2 * (K ω : ℝ)) P) :
    AEMeasurable (fun ω => (K ω : ℝ≥0∞)) P := by sorry
