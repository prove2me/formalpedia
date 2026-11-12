-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
-- name    : AvramDividend.Classical.avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:05:01.457086+00:00
-- url     : https://prove2.me/theorems/31370cd4-eda4-4f1a-b6b8-1c1ccbd40b5c
-- title:
--   Source-exact original two-noise stopped mesh limits are L1 and initially conditionally centred
-- statement:
--   Uniformly dominated predictable Gaussian and compensated-jump stopped finite-mesh gains converging almost surely to source limits are both integrable and have separate zero conditional expectations at time zero in the original filtration, without any additional measurability hypotheses.
-- source:
--   Proved 4c78399d dominated limit and 5428a9e7 integrable stopped mesh, plus pinned aestronglyMeasurable_of_tendsto_ae, Integrable.mono and le_of_tendsto.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_jb22_original_stopped_two_noise_dominated_mesh_limit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb23_original_stopped_two_noise_L1_initial_centered_limits
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (S : ℕ → Finset ι)
    (R J : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (hJint : ∀ u : ℝ≥0, Integrable (J u) P)
    (hJmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont u) P (J v) ω = J u ω)
    (a b : ℕ → ι → ℝ≥0)
    (WG WJ : ℕ → ι → Ω → ℝ)
    (hab : ∀ k, ∀ i ∈ S k, a k i ≤ b k i)
    (hWG : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WG k i))
    (hWJ : ∀ k, ∀ i ∈ S k,
      Measurable[𝓕.rightCont (a k i)] (WJ k i))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WG k i ω) *
          (R (b k i) ω - R (a k i) ω)) P)
    (hJprod : ∀ k, ∀ i ∈ S k,
      Integrable (fun ω =>
        (if τ ω ≤ a k i then 0 else WJ k i ω) *
          (J (b k i) ω - J (a k i) ω)) P)
    (Gseq Jseq : ℕ → Ω → ℝ)
    (hGsource : ∀ k ω, Gseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WG k i ω) *
        (R (b k i) ω - R (a k i) ω))
    (hJsource : ∀ k ω, Jseq k ω =
      ∑ i ∈ S k, (if τ ω ≤ a k i then 0 else WJ k i ω) *
        (J (b k i) ω - J (a k i) ω))
    (MG MJ BG BJ : Ω → ℝ)
    (hGconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Gseq k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P,
      Tendsto (fun k => Jseq k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖Gseq k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖Jseq k ω‖ ≤ BJ ω) :
    Integrable MG P ∧
    (P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable MJ P ∧
    (P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) := by sorry
