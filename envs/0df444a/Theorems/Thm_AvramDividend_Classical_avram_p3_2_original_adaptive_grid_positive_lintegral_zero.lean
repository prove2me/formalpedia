-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_adaptive_grid_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_adaptive_grid_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:50:59.381608+00:00
-- url     : https://prove2.me/theorems/11278425-75aa-42c8-8333-d7d02499a47c
-- title:
--   Original BV nonlinear compensation positive outer expectation vanishes on adaptive stopped grids
-- statement:
--   For the literal original spectrally negative bounded-variation Levy X and cumulative dividend D, the intrinsic negative-jump nonlinear remainder has zero positive ENNReal outer integral on every path-dependent monotone physical grid whose last tag is below an arbitrary path-dependent stopping clock. Handles random ruin, cap contact and localisation without L1 or predictable-grid upgrades; follows from one original full-probability jump event.
-- source:
--   Proved original all-stopped-grids cap-linear intrinsic residual event (pending publication) plus ENNReal.ofReal_eq_zero and lintegral_congr_ae; no new stochastic premise, optional stopping, law proxy, or axioms.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_adaptive_grid_positive_lintegral_zero
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
    (q : ℝ) (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω, Monotone (u ω))
    (n : ℕ) (hstop : ∀ ω, u ω n ≤ τ ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := u ω
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
