-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_generic_geometric_L1_gain_domination
-- name    : AvramDividend.Classical.avram_b24_generic_geometric_L1_gain_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:29:51.098763+00:00
-- url     : https://prove2.me/theorems/d44a39ba-e7db-4471-b7db-da4a9720637f
-- title:
--   Geometric L1 mesh increment bounds yield a.s. two-channel convergence and integrable uniform dominators
-- statement:
--   A generic measure-theoretic L1 summability lemma. Starting from integrable first gains, integrable increments and errors, and geometric bounds on the integrals of their norms, obtain almost-sure convergence of both gains, vanishing of the errors, and integrable pointwise uniform dominators. Independent of the Levy source. Genuine analysis step for B24.
-- source:
--   Tonelli, dominated series and almost-everywhere convergence from summable L1 norms.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_generic_geometric_L1_gain_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (G J E : ℕ → Ω → ℝ)
    (hG0 : Integrable (G 0) P) (hJ0 : Integrable (J 0) P)
    (hGI : ∀ k, Integrable (fun ω => G (k + 1) ω - G k ω) P)
    (hJI : ∀ k, Integrable (fun ω => J (k + 1) ω - J k ω) P)
    (hEI : ∀ k, Integrable (E k) P)
    (hGr : ∀ k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k)
    (hJr : ∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k)
    (hEr : ∀ k, (∫ ω, ‖E k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) :
    ∃ (MG MJ BG BJ : Ω → ℝ),
      (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω) := by sorry
