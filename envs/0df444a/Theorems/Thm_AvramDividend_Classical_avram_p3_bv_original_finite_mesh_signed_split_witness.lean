-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_finite_mesh_signed_split_witness
-- name    : AvramDividend.Classical.avram_p3_bv_original_finite_mesh_signed_split_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:59:40.227942+00:00
-- url     : https://prove2.me/theorems/f1b3a1e6-fbef-4d19-ab88-08e7cfe2fb63
-- title:
--   Original BV finite-mesh centred source-jump and HJB drift give signed stopped witness
-- statement:
--   The explicit common original mesh assumptions, two integrable dominators, a.e. limits, centred source jump means, nonpositive HJB drift means, and the actual finite-mesh dividend-reward bound together construct the precise integrable signed M/B witness. This is a conditional integration interface for the original stopped BV theorem and does not claim to establish the missing stochastic mesh hypotheses.
-- source:
--   The two new separately Proved bounded-variation mesh limit interfaces, together with elementary existential witness introduction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_mesh_pathwise_signed_upper_bound_limit
open MeasureTheory Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_bv_original_finite_mesh_signed_split_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (K : ℝ)
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
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Y ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ M' B' : Ω → ℝ,
      (Integrable M' P ∧ (∫ ω, M' ω ∂P) = 0) ∧
      (Integrable B' P ∧ (∫ ω, B' ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + M' ω + B' ω) := by sorry
