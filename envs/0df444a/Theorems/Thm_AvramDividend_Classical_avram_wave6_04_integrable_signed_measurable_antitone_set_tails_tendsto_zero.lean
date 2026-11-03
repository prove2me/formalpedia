-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
-- name    : AvramDividend.Classical.avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T06:31:57.763879+00:00
-- url     : https://prove2.me/theorems/8eac15a0-3e53-4504-bb37-fcf0743b43ff
-- title:
--   Integrable signed real kernel has vanishing integrals on decreasing measurable tails
-- statement:
--   For any real-valued integrable kernel on a measure space, restricting to a sequence of measurable sets decreasing to the empty set yields signed integrals converging to zero. The proof uses pointwise eventual vanishing of set indicators and dominated convergence with the integrable norm envelope. The lemma is intended for the actual original Lévy source intrinsic negative-jump count to promote almost-sure C2 Taylor summability to pathwise finite-band and large-negative-mark tail convergence; no stochastic compensator law is asserted.
-- source:
--   Wave6 Chat04 source-path cutoff support: finite signed integral tails vanish for antitone measurable sets by dominated convergence.

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ)
    (S : ℕ → Set α) (hSm : ∀ n, MeasurableSet (S n))
    (hAnti : Antitone S) (hEmpty : (⋂ n, S n) = ∅) :
    Tendsto (fun n : ℕ => ∫ x, (S n).indicator f x ∂μ)
      atTop (𝓝 0) := by sorry
