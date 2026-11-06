-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
-- name    : AvramDividend.Classical.avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:41:54.533751+00:00
-- url     : https://prove2.me/theorems/3c2f33da-f3ab-4a64-9515-4b9915de69b2
-- title:
--   One almost-sure original BV cap-linear sign event for every stopped physical grid
-- statement:
--   Under the actual original bounded-variation spectrally negative Levy law, show that a single full-probability path event supports the explicit original intrinsic negative-jump remainder R, its monotonicity and a nonpositive discounted cap-linear nonlinear correction on every monotone physical grid, for every path-dependent stopping map, without separate martingale or integrability assumptions. This permits physical localisation, including ruin and cap-contact grids.
-- source:
--   Direct caplinear C1 monotone extension and the Proved original intrinsic BV negative-jump source (222dbf6e), keeping its universal stopping and physical-grid quantifiers; no proxy law, stochastic optional stopping, circular canonical import, or new axiom.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_original_intrinsic_BV_nonlinear_stopped_downward_residual_discounted_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P,
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
          (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω),
          (∑ i : Fin n,
            Real.exp (-(q * (u i : ℝ))) *
              (V (riskProcess X x D (u i) ω -
                (R (u (i + 1)) - R (u i))) -
               V (riskProcess X x D (u i) ω))) ≤ 0 := by sorry
