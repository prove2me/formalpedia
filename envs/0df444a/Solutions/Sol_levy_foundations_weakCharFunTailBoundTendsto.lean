-- Prove2me | solution 1 for levy_foundations_weakCharFunTailBoundTendsto
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T11:10:00.407191+00:00
-- url     : https://prove2.me/submissions/2407f56e-0892-4b14-946e-84e8274bd581

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_levy_foundations_probabilityCharacteristicFun
import Definitions.Def_levy_foundations_weakCharFunTendsto
import Definitions.Def_levy_foundations_weakExpBCF

open MeasureTheory Complex ComplexConjugate Filter Topology BoundedContinuousFunction

theorem solution
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : φ 0 = 1) :
    Tendsto (fun r => 2⁻¹ * r *
      ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc : ContinuousAt (fun t => (1 : ℂ) - φ t) 0 := (continuous_const.sub hφc).continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.mp hc (ε / 4) (by positivity)
  refine ⟨2 / δ + 1, fun r hr => ?_⟩
  have hr0 : 0 < r := by
    have : 0 < 2 / δ := by positivity
    linarith
  have hrδ : 2 * r⁻¹ < δ := by
    have h1 : 2 / δ < r := by linarith
    rw [div_lt_iff₀ hδ] at h1
    rw [← div_eq_mul_inv, div_lt_iff₀ hr0]
    linarith
  have hbd : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖ ≤ ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Set.uIoc (-2 * r⁻¹) (2 * r⁻¹) := ht
    rw [Set.uIoc_of_le (by have : 0 < r⁻¹ := inv_pos.mpr hr0; linarith)] at ht'
    have habs : |t| < δ := by
      rw [abs_lt]
      constructor <;> [linarith [ht'.1]; linarith [ht'.2]]
    have := hδ' (show dist t 0 < δ by simpa using habs)
    rw [dist_eq_norm] at this
    simp only [hφ0, sub_self] at this
    simpa [dist_eq_norm] using this.le
  have hnn : 0 ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖ := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have habs2 : |2 * r⁻¹ - (-2 * r⁻¹)| = 4 * r⁻¹ := by
    have : 0 < r⁻¹ := inv_pos.mpr hr0
    rw [abs_of_nonneg (by linarith)]; ring
  rw [habs2] at hbd
  calc 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖
      ≤ 2⁻¹ * r * (ε / 4 * (4 * r⁻¹)) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
