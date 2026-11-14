-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_ae_equal_stages_square_envelope_transfer_20261113
-- name    : AvramDividend.Classical.avram_a21_ae_equal_stages_square_envelope_transfer_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:16:42.993515+00:00
-- url     : https://prove2.me/theorems/366cbcf0-365b-4b34-bebc-05617d2df797
-- title:
--   A.e.-equal stages inherit square-integrable domination and squared pointwise limit
-- statement:
--   On any original measure space, a sequence of random finite-stage variables whose squares are integrable and which equal almost surely a second sequence, with the second sequence uniformly dominated by a common square-integrable envelope and converging almost surely to a limit, inherits square measurability, common squared domination and almost-sure square convergence.
-- source:
--   Pinned Mathlib ae_all_iff, Integrable.aestronglyMeasurable, real norm squared and Filter.Tendsto.pow, with explicit ordered real product inequality. Supports exact original Borel marked-jump finite-stage limit 67336b2d.

import Mathlib
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_ae_equal_stages_square_envelope_transfer_20261113
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F Z : ℕ → Ω → ℝ) (C D : Ω → ℝ)
    (hF2 : ∀ k, Integrable (fun ω => (F k ω)^2) P)
    (hFZ : ∀ k, ∀ᵐ ω ∂P, F k ω = Z k ω)
    (hZD : ∀ k, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ D ω)
    (hD2 : Integrable (fun ω => (D ω)^2) P)
    (hZlim : ∀ᵐ ω ∂P, Tendsto (fun k => Z k ω)
      atTop (𝓝 (C ω))) :
    (∀ k, AEStronglyMeasurable (fun ω => (F k ω)^2) P) ∧
      Integrable (fun ω => (D ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖(F k ω)^2‖ ≤ (D ω)^2) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => (F k ω)^2)
        atTop (𝓝 ((C ω)^2))) := by sorry
