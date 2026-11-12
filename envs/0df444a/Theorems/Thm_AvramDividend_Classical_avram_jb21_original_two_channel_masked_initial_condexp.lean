-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_original_two_channel_masked_initial_condexp
-- name    : AvramDividend.Classical.avram_jb21_original_two_channel_masked_initial_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:23:11.737447+00:00
-- url     : https://prove2.me/theorems/5428a9e7-5835-40ee-bce1-77df8a5d6ce8
-- title:
--   Original stopped two-channel Gaussian and jump finite mesh has separately initially centred L1 gains
-- statement:
--   For the original right-continuous stopping time, masked Gaussian and compensated-jump deterministic mesh gains are separately integrable and conditionally centred at time zero. Requires only cellwise weighted product integrability, inherited source martingale conditional means, and stopped left-event measurability. This isolates the two-noise portion of the physical clipped Ito cash ledger.
-- source:
--   Depends on the original finite predictable initial conditional expectation certificate 0e39ef41 and proved original stopping-time masked finite grid sources c2585fb7. All stopping remains on original probability space.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_initial_condexp_finite_predictable_gain
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb21_original_two_channel_masked_initial_condexp
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
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hGprod : ∀ i ∈ S, Integrable
      (fun ω => (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)) P)
    (hJprod : ∀ i ∈ S, Integrable
      (fun ω => (if τ ω ≤ a i then 0 else WJ i ω) *
        (J (b i) ω - J (a i) ω)) P) :
    let MG : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (if τ ω ≤ a i then 0 else WG i ω) *
        (R (b i) ω - R (a i) ω)
    let MJ : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (if τ ω ≤ a i then 0 else WJ i ω) *
        (J (b i) ω - J (a i) ω)
    Integrable MG P ∧
    P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    Integrable MJ P ∧
    P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
