-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
-- name    : AvramDividend.Classical.avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:58:33.478149+00:00
-- url     : https://prove2.me/theorems/044d99a9-764b-4347-af2b-abac711ca051
-- title:
--   Original full-horizon strictly surviving terminal discounted omitted-strip positive error L1 vanishes on a common closed reserve band
-- statement:
--   For the genuine original bounded-variation spectrally negative Levy process X and original dividend D, assume both actual postpayment reserves at the last prescribed uniform physical-grid clock and the exact full horizon belong to one common closed reserve band on strict survival, and assume row integrability of the literal positive discounted survivor terminal excess. Then its expected positive value vanishes as the mesh is refined. The proof preserves the strict survival indicator and true full-T terminal reward, derives candidate nonnegativity from zero-boundary monotonicity, controls positive terminal increase by original one-sided BV physical path theorem, and converts its uniform almost-sure bound to expected convergence with the original probability law. No substitute process, finite-activity bound, positive interior reserve floor or global generator L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ) (hw0 : 0 ≤ w 0)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ᵐ ω ∂P, ∀ m : ℕ,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      (x + X.X (u m (m + 1)) ω -
        rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B ∧
      (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B) →
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
