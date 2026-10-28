-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_germ_zero_one_ws01f
-- name    : AvramDividend.Classical.levy_germ_zero_one_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T08:51:14.088635+00:00
-- url     : https://prove2.me/theorems/e1f28426-0fcf-40c9-835d-01933aff9e19
-- title:
--   Blumenthal zero-one law for the actual spectrally negative Lévy process germ
-- statement:
--   For every spectrally negative Lévy process in the canonical Avram structure, every event measurable in the time-zero path germ has probability zero or one. No Standing, Gaussian or bounded-variation hypothesis is needed. The proof derives measurable coordinates and origin continuity from the structure, and whole-future increment independence from the accepted finite-cylinder/filtration independence theorems, before invoking the separately remotely Proved general process germ zero-one law.
-- source:
--   Durrett, Probability: Theory and Examples, Blumenthal zero-one theorem; accepted Prove2Me general germ theorem 05828212 and accepted Lévy finite-cylinder independence df83d931/whole-future closure e87d68dd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_DurrettProbability_Brownian
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_whole_future_process_indep_past_of_finite_cylinders
import Theorems.Thm_AvramDividend_Classical_germ_zero_one_of_shift_independence_ws01f

open Filter MeasureTheory ProbabilityTheory DurrettProbability
open AvramDividend.Classical
open scoped NNReal Topology

theorem AvramDividend.Classical.levy_germ_zero_one_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {A : Set Ω} (hA : MeasurableSet[germSigma X.X] A) :
    P A = 0 ∨ P A = 1 := by sorry
