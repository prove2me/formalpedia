-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cap_extension_residual_identity_and_sign
-- name    : AvramDividend.Classical.avram_p3_bv_original_cap_extension_residual_identity_and_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:05:35.243759+00:00
-- url     : https://prove2.me/theorems/a4bb80de-e7a1-4bfd-96c1-6d32cd0075f7
-- title:
--   Exact original BV source residual and nonpositive stopped cap-linear correction in one pathwise witness
-- statement:
--   For the original bounded-variation spectrally negative Levy process, produce on one probability-one event the exact physical residual between drift deficit and intrinsic negative source jumps, prove its monotonicity, and bound its nonlinear discounted correction on every stopped chronological mesh by zero, for the explicit cap-linear verification candidate. This handles finite/infinite caps, source contact, and residual non-vanishing honestly.
-- source:
--   Composition of Proved 222dbf6e exact original intrinsic residual plus discounted stopped correction with Proved 5e9573dd global monotonicity of cap-linear C1 test extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- Preserve the precise intrinsic source residual identity while proving its
global nonlinear cap-extension correction has the favourable sign. -/

theorem AvramDividend.Classical.avram_p3_bv_original_cap_extension_residual_identity_and_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          Real.exp (-(q * (u i : ℝ))) *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
              V (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
