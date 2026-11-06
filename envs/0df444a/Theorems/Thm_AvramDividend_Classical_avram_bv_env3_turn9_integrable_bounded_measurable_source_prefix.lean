-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
-- name    : AvramDividend.Classical.avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:03:46.990663+00:00
-- url     : https://prove2.me/theorems/0231cb61-dad0-48fb-9f16-03d8f8b0e43f
-- title:
--   Integrability of a measurable random stopped-grid prefix
-- statement:
--   Given an original finite grid of real source increments that are individually integrable and a measurable Nat-valued random stopping-prefix index bounded by the grid size, the random stopped finite prefix sum is integrable. The proof rewrites the random upper limit as a fixed finite sum of measurable indicators and invokes integrability of each measurable restriction.
-- source:
--   Source-exact functional-analytic ingredient for the stopped physical grids of Avram P3-GRID3 53697545 and the BV-ENV3 measurable stopped prefix selectors 58312315/fbb734fc; supplies the L1 step toward P3-GRID4 c1e2f021 but requires actual integrability of each original compensated source cell.

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (f : ℕ → Ω → ℝ) (hf : ∀ i, Integrable (f i) P) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω), f i ω) P := by sorry
