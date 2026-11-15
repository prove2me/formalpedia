-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
-- name    : AvramDividend.Classical.avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:12:27.43521+00:00
-- url     : https://prove2.me/theorems/847ee51e-c7db-4185-96de-a5451abeab8d
-- title:
--   Any original noise gain sequence with integrable uniform envelope and almost sure limit is L1 Cauchy
-- statement:
--   For arbitrary real same-source gain functions G_n on any measure space, integrable each, with a single integrable envelope B bounding |G_n| almost everywhere and a pointwise almost-sure limit M, establish that M is integrable and the original sequence of gains is Cauchy in L1 in the explicit epsilon-N mean-absolute-difference sense. The result uses true a.e. measurability of the limit, integrable majorisation, dominated convergence of source differences to M, and integral triangle. It is reusable for original Gaussian/negative-mark stopped Itô-Meyer grids; no assumption of L2 Brownian law or a zero Lévy measure.
-- source:
--   Mathlib aestronglyMeasurable_of_tendsto_ae, Integrable.mono', Proved B24 source dominated convergence L1 vanishing.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_ae_convergent_integrably_dominated_original_gains_are_L1_cauchy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G : ℕ → Ω → ℝ) (M B : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P) (hBI : Integrable B P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ B ω)
    (hAE : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (M ω))) :
    Integrable M P ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ m l : ℕ, N ≤ m → N ≤ l →
          (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by sorry
