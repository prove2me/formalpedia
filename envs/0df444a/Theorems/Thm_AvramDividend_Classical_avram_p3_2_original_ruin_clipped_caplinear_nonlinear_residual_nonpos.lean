-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_ruin_clipped_caplinear_nonlinear_residual_nonpos
-- name    : AvramDividend.Classical.avram_p3_2_original_ruin_clipped_caplinear_nonlinear_residual_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:17:21.93669+00:00
-- url     : https://prove2.me/theorems/c2e041de-5c0b-413a-b126-3900e00ac8e1
-- title:
--   Original BV cap-linear negative residual stays nonpositive on the actual ruin-clipped chronological grid
-- statement:
--   For an actual original bounded-variation spectrally negative Lévy path and actual original controlled dividend reserve, every monotone physical grid can be clipped at the true ruin clock and finite horizon. The resulting cap-linear nonlinear residual from the intrinsic negative-jump-free source is nonpositive almost surely, including contact and ruin, without assuming the grid stays below the random stopping time beforehand.
-- source:
--   Source-exact strong stopped specialisation of the Proved original intrinsic BV global cap residual theorem 5e444532, retaining physical X/D and choosing ruin-clipped monotone grid v_i = min(u_i, min(ruinTime,T)).

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_global_cap_residual_grid_nonpositive
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_ruin_clipped_caplinear_nonlinear_residual_nonpos
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
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let v : ℕ → ℝ≥0 := fun i => min (u i) τ
      ∃ R : ℝ≥0 → ℝ,
        Monotone R ∧
        (∑ i : Fin n,
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by sorry
