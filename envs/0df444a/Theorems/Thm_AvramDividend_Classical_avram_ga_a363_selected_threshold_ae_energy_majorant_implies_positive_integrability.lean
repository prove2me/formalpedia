-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
-- name    : AvramDividend.Classical.avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:07:03.966227+00:00
-- url     : https://prove2.me/theorems/90bc6b73-2777-4b02-9179-d66af537c387
-- title:
--   A.e. Gaussian small-source positive energy and correction majorant implies integrability at the selected threshold
-- statement:
--   If the positive part of a measurable finite-mesh small-source residual at a selected cutoff δ is almost everywhere bounded by ε times a Gaussian raw energy E plus two integrable cross and discount error sources A and B, and E,A,B are integrable, then the selected small-source positive residual is integrable at every mesh level. This is the source-integrability part of the original selected-threshold Gaussian a361 requirement and does not assume integrability for all cutoffs.
-- source:
--   Original Gaussian a361 small full-cell source, a342 aestrong measurability, a243 raw energy integrability, a214 cross integrability and a284 discount source integrability.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a363_selected_threshold_ae_energy_majorant_implies_positive_integrability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℝ → ℕ → Ω → ℝ) (E A B : ℕ → Ω → ℝ)
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hSm : ∀ m, AEStronglyMeasurable
      (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hAI : ∀ m, Integrable (A m) P)
    (hBI : ∀ m, Integrable (B m) P)
    (hPt : ∀ m, ∀ᵐ ω ∂P,
      max (S δ m ω) 0 ≤ ε * E m ω + A m ω + B m ω) :
    ∀ m, Integrable (fun ω => max (S δ m ω) 0) P := by sorry
