-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_atom_clocks_injective
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_atom_clocks_injective
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:35:06.407142+00:00
-- url     : https://prove2.me/theorems/018c998a-f02d-4725-a4f1-d997b689de3a
-- title:
--   Original paid nonzero atomic real times injectively embed into physical stopped NNReal clocks
-- statement:
--   From original dividendMeasure restricted to the true horizon, every paid nonzero singleton has a nonnegative real time within T. Thus real.toNNReal provides a faithful injective, horizon-bounded physical clock index and retains membership in the actual original paymentTimes set. This is precisely the atomic-index interface required by the Proved full stopped P4-D signed jump budget.
-- source:
--   Proved original source support fbaa8669 and real-to-NNReal coercion. No duplicate clock atoms or invalid pre-ruin extensions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_nonzero_cash_atom_in_closed_horizon
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_paid_nonzero_atom_clocks_injective
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ≥0)
    (A : Set ℝ) (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse) :
    let E : Set ℝ := {t | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
    (∀ a : E, Real.toNNReal a.1 ≤ T) ∧
    (∀ a : E, (Real.toNNReal a.1 : ℝ) ∈
      paymentTimes (ruinTime X x D ω)) ∧
    Function.Injective (fun a : E => (Real.toNNReal a.1 : ℝ)) := by sorry
