-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18m_original_J_bounded_optional_sampling
-- name    : AvramDividend.Classical.avram_ja18m_original_J_bounded_optional_sampling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:22:36.540841+00:00
-- url     : https://prove2.me/theorems/850e34ce-8a84-469a-842a-ccd53b18daef
-- title:
--   Bounded stopping of original compensated jump martingale yields L1 and zero initial conditional expectation
-- statement:
--   Given original J deterministic L1 and right-continuous-filtration martingale, establish bounded stopping L1 and mean-zero from time zero. Handle actual càdlàg path regularity, bounded ruin-clock endpoints, original sample space; no large-mark second moment.
-- source:
--   JA18 decomposition 41babf55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18m_original_J_bounded_optional_sampling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
      (n : ℕ) (hn : 0 < n)
      (τ : Ω → ℝ≥0)
      (hτstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)))
      (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    (∀ t : ℝ≥0, Integrable (J t) P) →
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J t) ω = J s ω) →
    Integrable (fun ω => J (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => J (τ ω) ω) ω = 0) := by sorry
