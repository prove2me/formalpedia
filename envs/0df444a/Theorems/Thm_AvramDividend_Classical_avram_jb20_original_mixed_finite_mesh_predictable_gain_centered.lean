-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_mixed_finite_mesh_predictable_gain_centered
-- name    : AvramDividend.Classical.avram_jb20_original_mixed_finite_mesh_predictable_gain_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:20:10.941287+00:00
-- url     : https://prove2.me/theorems/012cc015-c7e3-4940-9280-e21842f4ecbd
-- title:
--   Both original Gaussian and compensated-jump finite predictable meshes have jointly integrable centred gain
-- statement:
--   On the unchanged physical probability space and right-continuous filtration, two original martingale noise channels with bounded predictable finite-grid weights give an integrable zero-mean combined stochastic sum. This is the mixed finite-grid first-order source term, prior to nonlinear Ito-Meyer passage.
-- source:
--   Apply the original Gaussian predictable finite mesh theorem to R and to the original compensated-jump martingale J, then use integrability and integral addition. Supports original mixed ruin-clipped cash ledger 544e8511.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_mesh_predictable_gain_centered
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_mixed_finite_mesh_predictable_gain_centered
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
    Integrable
      (fun ω =>
        (∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω)) +
        (∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω))) P ∧
    (∫ ω,
      (∑ i ∈ S, WG i ω * (R (b i) ω - R (a i) ω)) +
      (∑ i ∈ S, WJ i ω * (J (b i) ω - J (a i) ω)) ∂P) = 0 := by sorry
