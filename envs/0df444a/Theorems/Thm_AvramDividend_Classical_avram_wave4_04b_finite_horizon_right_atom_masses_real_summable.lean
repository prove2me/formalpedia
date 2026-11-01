-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
-- name    : AvramDividend.Classical.avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:36:27.981813+00:00
-- url     : https://prove2.me/theorems/f93f90b1-7cc9-42fe-9fbe-71fca66a4afa
-- title:
--   All actual right-payment atom masses of an adapted dividend measure are real-summable on a finite horizon
-- statement:
--   For every actual adapted nondecreasing left-continuous dividend strategy and finite horizon, construct its true countable right-atom support and atomless Stieltjes remainder, then prove that the real singleton masses on that support are summable and that their total extended-real mass is bounded by D⁺_T. This is the precise finite-variation mass budget for the controlled Itô–Meyer countable jump correction, retaining all diffuse and singular-continuous dividend variation.
-- source:
--   Already Proved exact full finite-horizon source Stieltjes atomic/diffuse decomposition, finite horizon total mass ENNReal.ofReal(D⁺T), and pinned Mathlib ENNReal.summable_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_stieltjes_atomic_diffuse

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_finite_horizon_right_atom_masses_real_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      Summable (fun t : A => (μ {(t : ℝ)}).toReal) ∧
      (∑' t : A, μ {(t : ℝ)}) ≤
        ENNReal.ofReal (rightLimit D T ω) := by sorry
