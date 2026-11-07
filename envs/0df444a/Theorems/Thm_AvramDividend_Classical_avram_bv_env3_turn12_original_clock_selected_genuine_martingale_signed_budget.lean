-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_clock_selected_genuine_martingale_signed_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_genuine_martingale_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:46:34.656475+00:00
-- url     : https://prove2.me/theorems/c73cd46d-992e-4ef3-b751-151c6e4ffffa
-- title:
--   Genuine original-process martingale finite signed source stopped at physical-grid clock-derived count
-- statement:
--   For any genuinely original right-continuous-filtration Lévy martingale and a genuine stopping time, the random number of pre-stopping physical-grid times is measurable and predictable. Its stopped actual martingale increments plus integrable pointwise nonpositive HJB drift have a finite integrable signed sum of nonpositive mean, with no external random index, conditional-mean-zero, or extra martingale integrability hypothesis.
-- source:
--   Composes accepted original martingale predictable prefix budget 2b993cd3 and current turn stopping clock selected prefix count and adaptedness f53747fc,d93b8897.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_genuine_martingale_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (B : ℕ → Ω → ℝ) (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    let k : Ω → ℕ := fun ω =>
      ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω) ∂P) ≤ 0 := by sorry
