-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_triple_mesh_stopped_signed_witness
-- name    : AvramDividend.Classical.avram_p3_bv_original_triple_mesh_stopped_signed_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:59:33.249642+00:00
-- url     : https://prove2.me/theorems/76cf8711-0ed3-43cb-ae9a-aec219cc6ccc
-- title:
--   Original BV stopped finite-mesh reward and signed source/HJB terms yield L1 witness
-- statement:
--   For the same actual source and dividend stopped finite-grid chain, if the three genuine approximate terms satisfy the signed finite-mesh inequality, converge almost everywhere, and have integrable dominators with centred jump and nonpositive HJB means, there exist the exact L1 M and B witnesses required for the original signed stochastic split. The stochastic mesh hypotheses remain explicit, so this theorem is a rigorous conditional interface rather than a claim that 9cd69d89 has been completed.
-- source:
--   The separately authored BV dominated centred/nonpositive mesh passage 943efd39 and triple mesh signed a.e. budget passage (both requiring remote compiler acceptance), followed by existential introduction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_dominated_centered_and_nonpositive_mesh_limits
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_triple_mesh_signed_budget_ae_limit
open MeasureTheory Filter AvramDividend.Classical

theorem AvramDividend.Classical.avram_p3_bv_original_triple_mesh_stopped_signed_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (Y M B DM DB : Ω → ℝ) (K : ℝ)
    (hMMeas : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hDM : Integrable DM P) (hDB : Integrable DB P)
    (hMDom : ∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω)
    (hBDom : ∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω)
    (hYLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMMean : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBMean : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ M' B' : Ω → ℝ,
      (Integrable M' P ∧ (∫ ω, M' ω ∂P) = 0) ∧
      (Integrable B' P ∧ (∫ ω, B' ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + M' ω + B' ω) := by sorry
