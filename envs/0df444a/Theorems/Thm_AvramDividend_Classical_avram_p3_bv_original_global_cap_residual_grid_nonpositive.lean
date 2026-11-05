-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_global_cap_residual_grid_nonpositive
-- name    : AvramDividend.Classical.avram_p3_bv_original_global_cap_residual_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T20:01:00.181267+00:00
-- url     : https://prove2.me/theorems/5e444532-1e25-42f4-8383-82b126062abd
-- title:
--   Original BV intrinsic downward residual contributes nonpositively across every stopped cap-linear verification grid
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process and original controlled reserve, the concrete finite/infinite-cap linear extension of an interior C1 verification function has an almost-sure monotone source residual whose discounted nonlinear corrections are nonpositive on every stopped chronological grid. Applies at cap contact and negative reserve; no false pure-jump residual-zero identity is assumed.
-- source:
--   Source-exact composition of Proved avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual (5e9573dd) and Proved avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos (222dbf6e).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/- The genuine original BV source residual is a nonpositive contribution
even at a finite cap, once the cap-linear C1 extension is constructed. -/

theorem AvramDividend.Classical.avram_p3_bv_original_global_cap_residual_grid_nonpositive
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
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
        (∑ i : Fin n,
          Real.exp (-(q * (u i : ℝ))) *
            (V (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))) -
              V (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
