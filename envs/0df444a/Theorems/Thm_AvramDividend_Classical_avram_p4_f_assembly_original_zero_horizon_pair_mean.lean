-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_zero_horizon_pair_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_zero_horizon_pair_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:22:26.99957+00:00
-- url     : https://prove2.me/theorems/813af4ea-f5c3-42e5-8be3-8c2158e6beec
-- title:
--   Exact original negative-band chronological factorial mean at zero horizon
-- statement:
--   At zero physical horizon, the original source negative-band marked jump set is empty pathwise, because every marked time must satisfy 0<u≤0. Hence its actual chronological pair count has zero expectation and is integrable, and (T ν(B))²=0. This closes the T=0 branch required by the unconditional original chronological pair mean d938e9a5, without a replacement stochastic model.
-- source:
--   Exact accepted original negative-band finite-time set e5e6f70b, full original d938e9a5 statement and standard measure-theoretic zero-integral identities; Mathlib pinned 0df444...

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_zero_horizon_pair_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω 0 n).toFinset
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    let r : ℝ :=
      ((((0 : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
    Integrable (fun ω => 2 * (K ω : ℝ)) P ∧
    (∫ ω, 2 * (K ω : ℝ) ∂P) = r ^ 2 := by sorry
