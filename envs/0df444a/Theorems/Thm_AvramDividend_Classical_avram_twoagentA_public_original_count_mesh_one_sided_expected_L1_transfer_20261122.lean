-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_count_mesh_one_sided_expected_L1_transfer_20261122
-- name    : AvramDividend.Classical.avram_twoagentA_public_original_count_mesh_one_sided_expected_L1_transfer_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T14:05:37.436873+00:00
-- url     : https://prove2.me/theorems/949a44de-2b21-4d9f-b68b-9573fc85a2e2
-- title:
--   Original signed-mark quantizer proof reusable original_count_mesh_one_sided_expected_L1_transfer_20261122
-- statement:
--   Republish the verbatim remotely accepted private proof as an independently importable PUBLIC original-physical negative-mark finite-band signed integral bridge helper, with the mathematical statement unchanged. The source has no private theorem imports.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_twoagentA_public_original_count_mesh_one_sided_expected_L1_transfer_20261122
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Finset ι) (N : ι → Ω → ℝ) (r δ : ι → ℝ)
    (hIntN : ∀ i ∈ S, Integrable (N i) P)
    (hMean : ∀ i ∈ S, (∫ ω, N i ω ∂P) = r i)
    (J Q : Ω → ℝ) (hJ : Integrable J P) (hQ : Integrable Q P)
    (hBound : ∀ᵐ ω ∂P, |J ω - Q ω| ≤
      ∑ i ∈ S, δ i * (N i ω + r i)) :
    (∫ ω, |J ω - Q ω| ∂P) ≤
      2 * (∑ i ∈ S, δ i * r i) := by sorry
