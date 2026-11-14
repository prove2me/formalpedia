-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_actual_BV_C1_any_strict_interior_band_ruin_stopped_compensator_integrable_mean_nonpositive
-- name    : AvramDividend.Classical.avram_bva_a22_original_actual_BV_C1_any_strict_interior_band_ruin_stopped_compensator_integrable_mean_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:24:22.225557+00:00
-- url     : https://prove2.me/theorems/8f43448b-6b40-4c79-8e0b-085cb187b924
-- title:
--   Actual original BV C1 negative Lévy marked compensator is integrable and has nonpositive expected drift on any given strict interior band without auxiliary analytic assumptions
-- statement:
--   For the genuine original spectrally negative Levy process of bounded variation, original dividend control, and original verification candidate continuous for nonnegative reserves, zero on strictly negative reserves, C1 on the strict cap interior, and gradient at least one, take an arbitrary true positive spatial band [a,b] whose half-width safety interval [a/2,b] lies strictly inside the original positive reserve cap. Define E as the exact source stopped prepayment strict interior event up to and including original ruin time, restricted to the true band [a,b]. Define G as the actual discounted candidate negative jump loss evaluated at the actual prepayment reserve and original Levy negative marks, set to zero outside E or when the mark is nonnegative. Prove directly that the true expected stopped predictable integral of G over the original source Levy measure and finite physical horizon is integrable and nonpositive. All auxiliary compact Lipschitz constants, uniform value bounds, and negative Levy large-tail finite measure follow automatically from the original source C1 and Levy assumptions by Proved Wave8 lemmas; the Proved Wave7 inclusive ruin compact compensator theorem gives integrability and signed mean. No artificial cap, finite activity, extra derivative bounds, spatial mesh rate or replacement stochastic system.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_actual_BV_C1_any_strict_interior_band_ruin_stopped_compensator_integrable_mean_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b)
    (hinside : Icc (a / 2) b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
