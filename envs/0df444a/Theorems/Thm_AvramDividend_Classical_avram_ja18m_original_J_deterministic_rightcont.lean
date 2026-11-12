-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18m_original_J_deterministic_rightcont
-- name    : AvramDividend.Classical.avram_ja18m_original_J_deterministic_rightcont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:22:36.304832+00:00
-- url     : https://prove2.me/theorems/ae114ec0-8047-48cd-bf48-d5eaa07424b5
-- title:
--   Original centred Lévy-minus-intrinsic residual J is a right-continuous filtration martingale at deterministic times
-- statement:
--   Prove original J(t)=X(t)-tE[X(1)]-R(t) has right-continuous-filtration deterministic-clock martingale conditional expectations. Standalone martingale algebra plus original Lévy independent increments; no stopping or quadratic moments.
-- source:
--   JA18 decomposition 41babf55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18m_original_J_deterministic_rightcont
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
        condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    let μ : ℝ := ∫ ω, X.X 1 ω ∂P
    let J : ℝ≥0 → Ω → ℝ :=
      fun t ω => X.X t ω - (t : ℝ) * μ - R t ω
    ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (J t) ω = J s ω := by sorry
