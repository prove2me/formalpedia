-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_contact_fourth_L1_from_cell_fourth_moments
-- name    : AvramDividend.Classical.avram_b24_contact_fourth_L1_from_cell_fourth_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:36:26.2352+00:00
-- url     : https://prove2.me/theorems/b0fb407d-8f51-4102-af03-404e950fd03a
-- title:
--   Expected fourth power of original terminal-contact noise bounded by sum of deterministic-cell fourth moments
-- statement:
--   Integrate the previously proved pathwise terminal-contact fourth-moment domination over the original probability measure. The fourth power of the unique random ruin-contact cell aggregate is controlled by the sum of the unconditional fourth moments of every deterministic interval; no false stopped-Gaussian increment independence is assumed. With integrability of the finite contact aggregate and each source cell, this replaces a random time/contact moment by deterministic source fourth-moment estimates and permits a mesh-size bound.
-- source:
--   Proved B24 unique terminal-contact fourth-power domination and Bochner finite-sum integral linearity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_mesh_fourth_moment_pathwise_dominance
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_contact_fourth_L1_from_cell_fourth_moments
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (S : Finset ℕ) (a b : ℕ → ℝ≥0) (σ : Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (hVI : ∀ i ∈ S, Integrable (fun ω => ‖V i ω‖ ^ 4) P)
    (hContactI : Integrable (fun ω =>
      ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i), V i ω‖ ^ 4) P) :
    (∫ ω, ‖∑ i ∈ S.filter (fun i => a i < σ ω ∧ σ ω ≤ b i),
        V i ω‖ ^ 4 ∂P) ≤
      ∑ i ∈ S, ∫ ω, ‖V i ω‖ ^ 4 ∂P := by sorry
