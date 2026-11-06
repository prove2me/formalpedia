-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_ae_dominated_mesh_residual_bridge
-- name    : AvramDividend.Classical.avram_p3_2_ae_dominated_mesh_residual_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:05:29.26395+00:00
-- url     : https://prove2.me/theorems/385f83ec-11ad-4e13-95e4-1b93f0e1448c
-- title:
--   Dominated original stopped mesh certificate gives a mean-nonpositive residual witness
-- statement:
--   An almost-sure original stopped mesh approximation Y_n of Y with two measurable dominated error components M_n and B_n whose expectations are respectively zero and nonpositive passes to a genuine integrable residual E=M+B with nonpositive mean and the limiting a.s. upper bound. This isolates the convergence step needed to integrate the original stochastic mesh certificate into canonical BV verification.
-- source:
--   Source-faithful direct consequence of original triple-mesh certificate db6a3111, through pinned Mathlib dominated convergence, measurability of a.e. limits and integral comparison. The child does not assert existence of a mesh or strengthen the stochastic hypotheses.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_ae_dominated_mesh_residual_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (K : ℝ) (Y : Ω → ℝ)
    (Ymesh Mmesh Bmesh : ℕ → Ω → ℝ)
    (M B DM DB : Ω → ℝ)
    (hMeasM : ∀ n, AEStronglyMeasurable (Mmesh n) P)
    (hMeasB : ∀ n, AEStronglyMeasurable (Bmesh n) P)
    (hIntDM : Integrable DM P) (hIntDB : Integrable DB P)
    (hDomM : ∀ n, ∀ᵐ ω ∂P, ‖Mmesh n ω‖ ≤ DM ω)
    (hDomB : ∀ n, ∀ᵐ ω ∂P, ‖Bmesh n ω‖ ≤ DB ω)
    (hYlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω)))
    (hMlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMzero : ∀ n, (∫ ω, Mmesh n ω ∂P) = 0)
    (hBupper : ∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0)
    (hGrid : ∀ᵐ ω ∂P, ∀ n,
      Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) :
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      ∀ᵐ ω ∂P, Y ω ≤ K + E ω := by sorry
