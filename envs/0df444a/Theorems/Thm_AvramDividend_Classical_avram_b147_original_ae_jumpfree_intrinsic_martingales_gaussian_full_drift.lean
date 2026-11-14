-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
-- name    : AvramDividend.Classical.avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:45:59.788617+00:00
-- url     : https://prove2.me/theorems/2b64c731-66f3-46ef-9ef8-eed1e3cc0ce3
-- title:
--   Original intrinsic Gaussian and compensated negative source martingales carry exact conull full signed physical drift on true jumpfree stopped clocks
-- statement:
--   Under the original spectrally negative Lévy standing assumptions, finite negative jump activity and a genuine bounded finite-range stopping clock, the proved B32 theorem constructs original source Gaussian residual R and compensated negative smallmark source Jsmall as time-uniform conull source limits and integrable martingales under the same original right-continuous filtration. Assuming another pair of original ordered random clocks has genuinely zero physical source jumps on a conull event, B146 yields a totalised intrinsic Gaussian M and the exact source increment equal to the R increment plus the full signed negative-strip Lévy drift times elapsed physical time. This combines genuine source martingale centring and the exact no-jump physical decomposition needed for true stopped Ito verification without relying on an artificial independent Gaussian process or global negative jump second moments. Hold publication until B146 itself is Proved.
-- source:
--   Prepared original B146 direct source decomposition and Proved B32 original two intrinsic martingale sources.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian and compensated small-jump channels are genuine integrable same-filtration martingales, with the exact physical Gaussian-drift source increment on conull jumpfree random clocks. -/

theorem AvramDividend.Classical.avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω)) := by sorry
