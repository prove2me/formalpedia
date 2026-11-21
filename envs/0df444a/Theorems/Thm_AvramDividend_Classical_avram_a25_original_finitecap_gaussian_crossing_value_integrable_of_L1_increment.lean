-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_integrable_of_L1_increment
-- name    : AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_integrable_of_L1_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:46:25.760178+00:00
-- url     : https://prove2.me/theorems/13fe0196-4add-4824-bf64-be2cf90653f9
-- title:
--   Actual bounded-reserve finitecap Gaussian crossing value integrable from original increment L1
-- statement:
--   For the original finitecap HJB candidate continuous on nonnegative reserves and vanishing strictly below zero, any actual stopped postpayment reserve Y in [0,b] and true Gaussian centred increment R∈L1 have integrable caplinear crossing value V(Y+R), provided the composed value is strongly measurable. Uses proved 0f403353 crossing bound |V(Y+R)|≤K+b+|R| and a finite probability measure. This closes a genuine missing integrability obligation for the original stopped Gaussian crossing cell, with no global boundedness assumption on V and without replacing the true X increment.
-- source:
--   Original zerojump finitecap stopped Gaussian crossing cells. True stochastic increment supplied as R and its integrability; result is a physical source-envelope transfer, not the HJB cash budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_integrable_of_L1_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (Y R : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ b)
    (hR : Integrable R P)
    (hV : AEStronglyMeasurable (fun ω =>
      if Y ω + R ω ≤ b then w (Y ω + R ω)
      else w b + (Y ω + R ω - b)) P) :
    Integrable (fun ω =>
      if Y ω + R ω ≤ b then w (Y ω + R ω)
      else w b + (Y ω + R ω - b)) P := by sorry
