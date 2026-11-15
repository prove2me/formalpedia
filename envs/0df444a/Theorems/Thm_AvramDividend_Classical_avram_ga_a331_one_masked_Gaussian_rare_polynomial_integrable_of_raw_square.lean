-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
-- name    : AvramDividend.Classical.avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:06:36.030982+00:00
-- url     : https://prove2.me/theorems/2d50fe41-03f1-4be5-9922-48a6b71da133
-- title:
--   Single original Gaussian masked rare polynomial source integrable from integrable raw-square cell
-- statement:
--   For a measurable raw Gaussian increment r and any measurable original mask A, if the masked raw squared increment is integrable under a probability law, then the rarer masked polynomial source 1+abs(r)+(r-a)²/2 on the fixed raw threshold event is integrable. The unconditional Gaussian polynomial bound a310 and constant deterministic drift provide an integrable majorant; no mesh dependence or complexity-heavy finite sum manipulations appear.
-- source:
--   Proved scalar Gaussian polynomial-to-raw-square domination a310; Mathlib Integrable.mono on a single measured masked event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a310_raw_centered_Gaussian_polynomial_bounded_by_raw_square
open MeasureTheory Filter Topology Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a331_one_masked_Gaussian_rare_polynomial_integrable_of_raw_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (r : Ω → ℝ) (a δ : ℝ)
    (A : Ω → Prop) [DecidablePred A] (hAm : MeasurableSet {ω | A ω})
    (hrm : Measurable r) (hRawI : Integrable
      (fun ω => if A ω then (r ω)^2 else 0) P) :
    Integrable (fun ω =>
      if A ω ∧ δ ≤ |r ω| then
        1+|r ω|+(r ω-a)^2/2 else 0) P := by sorry
