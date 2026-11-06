-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_stopped_discounted_prejump_gradient_cell_exact_quadratic_nu
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_prejump_gradient_cell_exact_quadratic_nu
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:32:54.181084+00:00
-- url     : https://prove2.me/theorems/cf0dfc8e-7b88-4c54-aad7-269a65fc68fe
-- title:
--   Actual original stopped derivative grid cell exact quadratic Lévy ν-energy and zero mean
-- statement:
--   On a cell of the actual original X's intrinsic negative marked jump process, the stopped (left-endpoint) discounted clipped derivative of w at the original controlled reserve left limit is strongly measurable on the physical right-continuous filtration. Its compensated marked count has exact L² ν-energy r∫H² and zero terminal expectation. This provides a quantitative physical source energy estimate under genuine stopping and clipping, retaining ν and the same process; no infinite-cutoff claim.
-- source:
--   Use the actual controlled pre-jump reserve predictable source and original discounted gradient/clipping predictability to establish time-s measurable bounded coefficients, including the true stopping event. Invoke the Proved original full negative-cutoff weighted isometry and original conditional compensated martingale step. The conclusion supplies an exact quadratic ν-integral energy, not only abstract MemLp.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_discounted_deriv_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_stopped_discounted_prejump_gradient_cell_exact_quadratic_nu
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (s T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    let H : Ω → ℝ := fun ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0) then 0
      else max (-K) (min K (Real.exp (-(q * (s : ℝ))) *
        deriv w (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) s)))
    let Z : Ω → ℝ := fun ω => H ω * ((N ω).toReal - r)
    MemLp Z 2 P ∧
    (∫ ω, (Z ω) ^ 2 ∂P) = r * (∫ ω, (H ω) ^ 2 ∂P) ∧
    (∫ ω, Z ω ∂P) = 0 := by sorry
