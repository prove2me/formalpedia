-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_explicit_ruin_cap_BV_residual
-- name    : AvramDividend.Classical.avram_p3_2_original_explicit_ruin_cap_BV_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:42:56.533945+00:00
-- url     : https://prove2.me/theorems/dac87ae6-3014-4491-a473-5e83b37b7a35
-- title:
--   Explicit original BV intrinsic residual formula has nonpositive cap-contact ruin-stopped grid contribution
-- statement:
--   On the literal original bounded-variation spectrally negative Lévy path and controlled reserve, define R(t) as drift minus X(t) minus the actual ENNReal negative-jump mass sum. On the original ruin-clipped time grid the explicitly defined residual is monotone and its discounted nonlinear correction for the cap-linear C1 extension is nonpositive, including cap contact and ruin. This exposes the exact measurable source expression for future L1 construction.
-- source:
--   Combines two public Proved original-source parents, positive-cap global monotonicity 5e9573dd and intrinsic source-residual exact formula/sign 222dbf6e. Retains the exact intrinsic negative-jump ENNReal mass sum and the actual ruin-clipped physical time grid without surrogate laws.

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

theorem AvramDividend.Classical.avram_p3_2_original_explicit_ruin_cap_BV_residual
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
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0,
            if 0 < s ∧ s ≤ t then
              ENNReal.ofReal
                (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      Monotone R ∧
        (∑ i : Fin n,
          Real.exp (-(q * (v i : ℝ))) *
            (V (riskProcess X x D (v i) ω -
              (R (v (i + 1)) - R (v i))) -
             V (riskProcess X x D (v i) ω))) ≤ 0 := by sorry
