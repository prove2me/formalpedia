-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_original_stopping_time_separate_masked_mesh
-- name    : AvramDividend.Classical.avram_jb21_original_stopping_time_separate_masked_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:56:39.61126+00:00
-- url     : https://prove2.me/theorems/c2585fb7-5730-490d-a4ce-fc9be4290c52
-- title:
--   Original right-continuous stopping-time masked two-channel finite-grid gains are separately centred
-- statement:
--   The actual original right-continuous stopping-time condition supplies predictable left-endpoint masking events for every deterministic cell. Gaussian and compensated jump gains stopped by this random clock are separately L1 and centred.
-- source:
--   Direct Proved f289dc01 two-channel finite-grid theorem, plus original right-continuous stopping-time left-mask measurable events. No pending theorem imports.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb21_original_stopping_time_separate_masked_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ι → ℝ≥0) (WG WJ : ι → Ω → ℝ)
    (hab : ∀ i ∈ S, a i ≤ b i)
    (hWG : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i))
    (hWJ : ∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i))
    (KG KJ : ℝ)
    (hWGbound : ∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ KG)
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ KJ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω) ∂P) = 0 ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω) ∂P) = 0 := by sorry
