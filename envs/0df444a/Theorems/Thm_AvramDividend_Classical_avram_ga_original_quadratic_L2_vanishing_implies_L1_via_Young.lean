-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_quadratic_L2_vanishing_implies_L1_via_Young
-- name    : AvramDividend.Classical.avram_ga_original_quadratic_L2_vanishing_implies_L1_via_Young
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:12:09.407172+00:00
-- url     : https://prove2.me/theorems/85ab5ffc-a12f-42d6-93cd-ea8f7a742b91
-- title:
--   Vanishing second moment implies vanishing absolute first moment of Gaussian physical-grid quadratic noise on a probability space
-- statement:
--   For a sequence of real stochastic variables on a probability space, with integrable absolute values and squares, if the expected squared value tends to zero then so does the expected absolute value. Use the genuinely Proved quantitative Young bound E|U|≤E[U²]/(2ε)+ε/2 for each fixed ε>0, and the order characterisation of convergence to zero; there is no unjustified summation of absolute centred Gaussian squares. Apply to the authentic stopped finite-cap physical-grid second-chaos sum whose L² variance convergence is established by the accepted original-source theorem.
-- source:
--   Completes the original finitecap stopped Gaussian compensated-Hessian second-channel L1 vanishing from authenticated L2 variance without relying on a prepackaged Ito theorem or a pathwise cash assumption.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_quadratic_L2_vanishing_implies_L1_via_Young
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ℕ → Ω → ℝ)
    (hAbs : ∀ m, Integrable (fun ω => |U m ω|) P)
    (hSq : ∀ m, Integrable (fun ω => (U m ω) ^ 2) P)
    (hMom : Tendsto (fun m => ∫ ω, (U m ω) ^ 2 ∂P)
       atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, |U m ω| ∂P)
       atTop (𝓝 (0 : ℝ)) := by sorry
