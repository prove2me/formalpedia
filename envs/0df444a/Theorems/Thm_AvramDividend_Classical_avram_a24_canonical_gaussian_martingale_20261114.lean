-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_martingale_20261114
-- name    : AvramDividend.Classical.avram_a24_canonical_gaussian_martingale_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:11:21.953209+00:00
-- url     : https://prove2.me/theorems/86d89070-1ead-4606-b979-878b41b4f607
-- title:
--   Canonical original globally adapted Gaussian residual preserves physical conditional-expectation martingale law
-- statement:
--   A physical intrinsic Gaussian residual limit which is a martingale in the original right-continuous filtration has a globally raw-adapted exact zero-origin representative with the same martingale property.
-- source:
--   Proved source F_t adapted canonical G and pinned Mathlib condExp_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original physical Gaussian martingale property transfers to a globally adapted canonical source. -/

theorem AvramDividend.Classical.avram_a24_canonical_gaussian_martingale_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
