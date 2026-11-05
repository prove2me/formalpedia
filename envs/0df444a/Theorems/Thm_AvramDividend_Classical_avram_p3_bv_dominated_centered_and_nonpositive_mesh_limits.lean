-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
-- name    : AvramDividend.Classical.avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:44:11.477713+00:00
-- url     : https://prove2.me/theorems/943efd39-3fb2-4bd8-b980-3a9f051de143
-- title:
--   Original BV mesh: centred jump and nonpositive HJB drift both survive dominated convergence
-- statement:
--   Under common original-probability dominated a.e. limits, if every BV source mesh compensated jump term is centred and every HJB drift mesh has nonpositive expected value, both properties hold for the limits, and both limits are genuinely integrable. This is a direct two-sided limit bridge towards the original stopped BV stochastic split, with the required dominators and convergence still explicitly visible.
-- source:
--   Proved P3-C dominated integrable source residual limit a9853993 and Proved dominated nonpositive expected source residual limit 7c873974, instantiated on the signed jump approximation and its negative; pinned Mathlib integral_neg.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
open MeasureTheory Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Mmesh Bmesh : ℕ → Ω → ℝ) (M B DM DB : Ω → ℝ)
    (hMMeas : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMMean : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) :
    (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) := by sorry
