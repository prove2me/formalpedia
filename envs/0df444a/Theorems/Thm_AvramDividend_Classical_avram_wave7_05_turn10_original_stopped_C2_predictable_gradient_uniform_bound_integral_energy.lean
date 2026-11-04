-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
-- name    : AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:53:04.38425+00:00
-- url     : https://prove2.me/theorems/b5a491b3-ddf1-4493-b395-9772e11315ff
-- title:
--   Original stopped C2 predictable reserve gradient with pointwise cap has uniformly bounded integrated quadratic energy
-- statement:
--   Under the canonical original SpectrallyNegativeLevy X, dividend strategy D, right-continuous filtration and genuine ruin time, every stopped predictable discounted C2 reserve gradient with uniform deterministic pointwise bound K has an integrable square and integrated square at most K squared. This turns pointwise truncation into the exact energy hypothesis for the stopped Gaussian one-cell variance bound.
-- source:
--   Canonical AvramDividend.Classical source, already proved joint measurability/predictability of stopped controlled gradient, integrability domination and the original probability measure.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn10_original_stopped_C2_predictable_gradient_uniform_bound_integral_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n ω ≤ s})
    (G : ℕ → Ω → ℝ)
    (hGsource : ∀ n, G n = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ n ω : WithTop ℝ≥0)))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ n ω, |G n ω| ≤ K) :
    ∀ n, Integrable (fun ω => G n ω * G n ω) P ∧
      (∫ ω, G n ω * G n ω ∂P) ≤ K ^ 2 := by sorry
