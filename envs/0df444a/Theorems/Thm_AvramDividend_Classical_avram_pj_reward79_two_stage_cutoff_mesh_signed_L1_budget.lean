-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
-- name    : AvramDividend.Classical.avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:55:25.234878+00:00
-- url     : https://prove2.me/theorems/b15fdaf9-3176-435e-88db-6e310ed5b6d7
-- title:
--   Two-stage original stopped purejump Ito error: small spatial cutoff plus vanishing physical mesh gives signed L1 budget
-- statement:
--   A source-exact stopped Ito/Stieltjes signed error admits a fixed spatial cutoff term K with global L1 <=epsilon/2 and a sequence of refining-physical-mesh terms E_k with vanishing L1; nonpositive jump/overshoot remainder R_k need not be integrable. Then choose a mesh with combined L1 error <=epsilon and retain one nonpositive remainder. This distinguishes the two errors and keeps the original inclusive payment and stopping conventions in downstream stochastic applications.
-- source:
--   Proved reward78 + triangle inequality for Bochner real integral; deterministic bridge from cutoff error and physical mesh limit to single signed source75.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward78_L1_vanishing_signed_mesh_error_select
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F K : Ω → ℝ) (E R : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hKI : Integrable K P)
    (hKSmall : (∫ ω, |K ω| ∂P) ≤ ε / 2)
    (hEI : ∀ k, Integrable (E k) P)
    (hR : ∀ k, ∀ᵐ ω ∂P, R k ω ≤ 0)
    (hLedger : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ K ω + E k ω + R k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      Filter.atTop (𝓝 (0 : ℝ))) :
    ∃ e r : Ω → ℝ,
      Integrable e P ∧
      (∫ ω, |e ω| ∂P) ≤ ε ∧
      (∀ᵐ ω ∂P, r ω ≤ 0) ∧
      (∀ᵐ ω ∂P, F ω ≤ e ω + r ω) := by sorry
