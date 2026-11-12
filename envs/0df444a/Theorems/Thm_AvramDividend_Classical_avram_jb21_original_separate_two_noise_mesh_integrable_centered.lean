-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_original_separate_two_noise_mesh_integrable_centered
-- name    : AvramDividend.Classical.avram_jb21_original_separate_two_noise_mesh_integrable_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:42:48.812109+00:00
-- url     : https://prove2.me/theorems/f289dc01-b8b7-40a4-a713-734df09429bc
-- title:
--   Original mixed finite grid has separately integrable centred Gaussian and compensated-jump gains
-- statement:
--   Each of the two original filtration predictable bounded-weight finite mesh gains is separately integrable with zero expectation, providing distinct Gaussian and compensated-jump witnesses for the stopped Ito cash ledger.
-- source:
--   Direct applications of Proved 3433d16a original Gaussian finite-mesh theorem separately to R and J. Original right-continuous filtration; no replacement process.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb21_original_separate_two_noise_mesh_integrable_centered
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
    (hWJbound : ∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ KJ) :
    Integrable (fun ω => ∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω)) P ∧
    Integrable (fun ω => ∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω)) P ∧
    (∫ ω, ∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω) ∂P) = 0 ∧
    (∫ ω, ∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω) ∂P) = 0 := by sorry
