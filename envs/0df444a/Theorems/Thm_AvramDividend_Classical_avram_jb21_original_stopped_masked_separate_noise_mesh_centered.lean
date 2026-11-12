-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_original_stopped_masked_separate_noise_mesh_centered
-- name    : AvramDividend.Classical.avram_jb21_original_stopped_masked_separate_noise_mesh_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:54:40.74207+00:00
-- url     : https://prove2.me/theorems/ecfd5898-fe9a-47d4-ac61-06ad1ccb0604
-- title:
--   Original two-channel stopped-left-endpoint finite grid has separate integrable centred gains
-- statement:
--   At a random stopping clock, retain only deterministic-mesh Gaussian and compensated-jump increments whose left endpoint precedes that clock. The past-event masks are measurable in the original right-continuous filtration. Both resulting gains are separately integrable and centred.
-- source:
--   Proved f289dc01 two-noise separate mesh certificate; filtration-measurable past masks and uniform predictable weight bounds. Discrete approximation of actual stopped Ito ledger 544e8511.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb21_original_stopped_masked_separate_noise_mesh_centered
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
    (hτpast : ∀ i ∈ S,
      MeasurableSet[𝓕.rightCont (a i)] {ω | τ ω ≤ a i}) :
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω) ∂P) = 0 ∧
    (∫ ω, ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) * (J (b i) ω - J (a i) ω) ∂P) = 0 := by sorry
