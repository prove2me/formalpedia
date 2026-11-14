-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb70_integrable_component_envelopes_majorise_compensated_positive_cash_residual
-- name    : AvramDividend.Classical.avram_bvb70_integrable_component_envelopes_majorise_compensated_positive_cash_residual
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T14:48:19.614323+00:00
-- url     : https://prove2.me/theorems/5c2bfc8f-4c58-4a30-91f1-e643f0dea3d9
-- title:
--   Common integrable component envelopes yield original compensated cash positive-residual L1 dominator
-- statement:
--   Given random physical dividend cash rows F_n, negative-jump mark rows J_n and compensator rows V_n with uniformly integrable component envelopes and individually integrable rows, the one-sided positive compensated cash discrepancy max(F_n - (b+J_n−V_n),0) is measurable P-almost everywhere and dominated for all n by the same explicit integrable sum of envelopes and |b|. Applies to the exact original BVB66 source once source-specific original F full-T, J Poisson count and V finite-rate bounds are established.
-- source:
--   Triangle inequality, Integrable.add/max, original top-cap BVB66 component envelope decomposition

import Mathlib
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb70_integrable_component_envelopes_majorise_compensated_positive_cash_residual
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F J V : ℕ → Ω → ℝ) (b : ℝ)
    (Fbound Jbound Vbound : Ω → ℝ)
    (hFi : Integrable Fbound P) (hJi : Integrable Jbound P)
    (hVi : Integrable Vbound P)
    (hFRows : ∀ n, Integrable (F n) P)
    (hJRows : ∀ n, Integrable (J n) P)
    (hVRows : ∀ n, Integrable (V n) P)
    (hFdom : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ Fbound ω)
    (hJdom : ∀ n, ∀ᵐ ω ∂P, ‖J n ω‖ ≤ Jbound ω)
    (hVdom : ∀ n, ∀ᵐ ω ∂P, ‖V n ω‖ ≤ Vbound ω) :
    let E : ℕ → Ω → ℝ := fun n ω =>
      max (F n ω - (b + (J n ω - V n ω))) 0
    ∃ Henv : Ω → ℝ,
      Integrable Henv P ∧
      (∀ n, AEStronglyMeasurable (E n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, ‖E n ω‖ ≤ Henv ω) := by sorry
