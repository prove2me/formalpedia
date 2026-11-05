-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_concrete_stopped_nonlinear_mean_zero
-- name    : AvramDividend.Classical.avram_p3_e_compensator_original_concrete_stopped_nonlinear_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:18:38.181293+00:00
-- url     : https://prove2.me/theorems/15ee174f-bde5-408b-8c34-17db0de55606
-- title:
--   Original BV stopped nonlinear compensated jump mean zero with concrete kernels
-- statement:
--   For the literal original Lévy jump measure of X and a bounded right-continuous-filtration stopping time, the discounted nonlinear negative-jump integral, restricted to an explicitly predictable compact interior region, has an integrable centred compensated residual with expectation exactly zero. All source jump, time-mark kernel, process-law binding and stopped-integrand definitions are constructed, rather than assumed as parameters. The remaining predictable-region, stopping-time and compact Lipschitz hypotheses are explicit, for P3-G and canonical P3 to discharge.
-- source:
--   Source exact literal original stopped-jump result 73b13e71 (Proved) together with original predictable rectangle theorem 393b03a8, original negative Borel rate 34dbea70 and arbitrary Borel rate 859bf7be (all Proved, inspected 4 November 2026). Concrete NX, K, MK, MT, G and H are defined by the original X,D, 𝓕.rightCont and X.ν; no independent compensator axiom, Poisson replacement or canonical-target edit.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_NX_stopped_jump_mean_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_e_compensator_original_concrete_stopped_nonlinear_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧
    (∫ ω,
      ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
       (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
         ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by sorry
