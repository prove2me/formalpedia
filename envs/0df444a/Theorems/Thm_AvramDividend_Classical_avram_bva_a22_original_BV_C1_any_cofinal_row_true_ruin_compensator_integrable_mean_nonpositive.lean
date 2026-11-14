-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_C1_any_cofinal_row_true_ruin_compensator_integrable_mean_nonpositive
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_C1_any_cofinal_row_true_ruin_compensator_integrable_mean_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:29:42.028192+00:00
-- url     : https://prove2.me/theorems/760e5db6-e07b-434c-a089-f5c697100774
-- title:
--   Every original arbitrary cofinal BV spatial row has an integrable nonpositive true stopped negative Lévy mark compensator with no auxiliary analytic hypotheses
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy source X, true dividend D, true first ruin clock, verification candidate C1 in the strict cap interior, and ANY prescribed spatial row sequences a_n,b_n with 0<a_n<=2, a_n<=b_n and the genuine safety half-band [a_n/2,b_n] strictly within cap C, prove for every original row n that the inclusive-ruin stopped source negative-mark compensator kernel over physical horizon T is absolutely integrable and has nonpositive expectation. E_n is the actual stopped prepayment interior event and G_n is the exact discounted candidate value loss on true X negative jump marks. The already Proved original analytic certificate yields each row finite compact Lipschitz L_n, candidate bound R_n, and finite true Levy mark intensity beyond a_n/2, without any extra assumptions or finite activity. Apply the original Proved Wave7 inclusive-ruin compensator theorem rowwise. This establishes the signed generator source leg simultaneously on the actual arbitrary bands and original T; it does not yet establish the remaining open physical-mesh spatial positive-error L1 convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_any_interior_C1_band_automatic_negative_mark_compensator_analytic_certificate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_compact_negative_jump_expected_nonpos
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_C1_any_cofinal_row_true_ruin_compensator_integrable_mean_nonpositive
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
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (ha2 : ∀ n, a n ≤ 2)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C}) :
    ∀ n : ℕ,
    let E : Set (ℝ≥0 × Ω) := {p |
      ((p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C) ∧
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
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
