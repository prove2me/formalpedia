-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_explicit_ruin_cap_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_explicit_ruin_cap_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:27:05.500561+00:00
-- url     : https://prove2.me/theorems/839e0ed0-0a4b-4a75-b7d3-a16b346a355c
-- title:
--   Literal original BV ruin-stopped intrinsic nonlinear residual has zero positive outer mass
-- statement:
--   For the original bounded-variation spectrally negative Levy process X and actual controlled reserve X/D, the capped C1 extension's discounted nonlinear signed correction from the explicitly defined original negative-jump residual R has zero ENNReal positive-part lintegral on any true ruin-and-horizon clipped monotone physical time grid. No L1 integrability or proxy process is assumed.
-- source:
--   Direct consequence of public Proved original explicit intrinsic residual dac87ae6, with literal original jumps, cap contact, true ruin time and horizon, and nonpositive integral of ENNReal.ofReal signed residual. No L1 upgrade.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_explicit_ruin_cap_BV_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_explicit_ruin_cap_positive_lintegral_zero
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
    (q : ℝ) (T : ℝ≥0) (u : ℕ → ℝ≥0)
    (hu : Monotone u) (n : ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u i) τ
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∑ i : Fin n,
        Real.exp (-(q * (v i : ℝ))) *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by sorry
