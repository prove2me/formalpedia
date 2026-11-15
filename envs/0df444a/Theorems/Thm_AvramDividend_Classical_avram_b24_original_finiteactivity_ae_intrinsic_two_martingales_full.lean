-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_ae_intrinsic_two_martingales_full
-- name    : AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_martingales_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:22:49.660265+00:00
-- url     : https://prove2.me/theorems/37855066-0694-414c-8619-abc4317fe3da
-- title:
--   Original finiteactivity arbitrary intrinsic Gaussian and compensated smallmark AE representatives are both martingales under right-continuous filtration
-- statement:
--   Original Standing finiteactivity X: R and Jsmall arbitrary physical-time AE representatives of original Gaussian truncated residual and compensated small-band intrinsic processes. Establish each R_t and Jsmall_t integrable and prove both actual right-continuous filtration martingale conditional expectation identities at all deterministic s≤t. Use Proved b133 canonical alltime two-martingale source at zero stopping clock and original intrinsic limit uniqueness; transfer conditional expectation via condExp_congr_ae. This is stronger than the already Proved integrability-only 97d70e1c and supports original ruinclipped Itô mesh source e44e5a0b.
-- source:
--   Proved 2e2cb641 original intrinsic two-martingale witness and Mathlib tendsto_nhds_unique and Integrable.congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_finiteactivity_ae_intrinsic_two_martingales_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) :
    (∀ u : ℝ≥0, Integrable (R u) P) ∧
    (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
    (∀ a b : ℝ≥0, a ≤ b →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
    (∀ a b : ℝ≥0, a ≤ b →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) := by sorry
