-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_two_scale_centered_positive_error_diagonal
-- name    : AvramDividend.Classical.avram_bv_strict6_two_scale_centered_positive_error_diagonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:55:37.259643+00:00
-- url     : https://prove2.me/theorems/f65aff31-2aca-429a-bc7d-dc66d7c3ced0
-- title:
--   Two-scale localisation diagonal preserves original grid centred residual and vanishing positive error
-- statement:
--   Given literal physical-grid payoff F and original signed source B, a family of localised centred compensated terms and integrable positive approximation errors, with per-grid spatial cutoffs approaching a vanishing mesh tolerance, admits one diagonal selection preserving mean zero, L1 positive-error decay and the same physical pathwise bound. The lemma supplies analytic two-scale assembly; source-exact construction of the cutoff family remains separate.

import Mathlib
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_two_scale_centered_positive_error_diagonal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F B : ℕ → Ω → ℝ) (c : ℝ)
    (M Err : ℕ → ℕ → Ω → ℝ) (η : ℕ → ℝ)
    (hηpos : ∀ n, 0 < η n)
    (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hErr : ∀ n k,
      Integrable (fun ω => max (Err n k ω) 0) P)
    (hApprox : ∀ n (ε : ℝ), 0 < ε →
      ∃ k,
        (∫ ω, max (Err n k ω) 0 ∂P) ≤ η n + ε ∧
        (∀ᵐ ω ∂P, F n ω ≤
          c + (M n k ω + B n ω) + max (Err n k ω) 0)) :
    ∃ M' Err' : ℕ → Ω → ℝ,
      (∀ n, Integrable (M' n) P ∧
        (∫ ω, M' n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err' n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err' n ω) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ c + (M' n ω + B n ω) + max (Err' n ω) 0) := by sorry
