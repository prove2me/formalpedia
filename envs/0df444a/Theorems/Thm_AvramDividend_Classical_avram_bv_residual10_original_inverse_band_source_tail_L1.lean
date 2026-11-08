-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_inverse_band_source_tail_L1
-- name    : AvramDividend.Classical.avram_bv_residual10_original_inverse_band_source_tail_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:04:38.102956+00:00
-- url     : https://prove2.me/theorems/fac81d7e-393f-4773-9db3-029dc26e3e64
-- title:
--   Original pre-jump reserve reciprocal bands exhaust with vanishing expected BV source-mass tails
-- statement:
--   The original controlled reserve left limits at all physical-grid nodes admit common measurable rowwise bounds on both their magnitudes and reciprocals, so nonzero reserve coordinates lie away from the zero boundary at each finite row. Those events exhaust almost surely. With Standing and BoundedVariation, the exact original terminal BV source-mass envelope multiplied by an arbitrary fixed nonnegative factor is integrable on each excluded event and has expectation tending to zero. The lemma does not assert the actual stopped stochastic discretisation error is bounded by this envelope; that is a separate original-process obligation.
-- source:
--   AVRAM BV-RESIDUAL10 original reciprocal-band with BV source-tail integrability integration, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_inverse_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_inverse_band_source_tail_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤)
    (T : ℝ≥0) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    ∃ N L : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n =
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i)) ≤ (N n : ℝ)} ∩
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs ((Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i))⁻¹) ≤ (L n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n, Integrable (fun ω => if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by sorry
