-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_scale_positive_excess_of_cell_and_contact
-- name    : AvramDividend.Classical.avram_bv_strict10_two_scale_positive_excess_of_cell_and_contact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:25:28.280361+00:00
-- url     : https://prove2.me/theorems/f75859f9-6c92-4b47-b5c7-81fbcf255aac
-- title:
--   Two-scale original BV contact and C1 errors imply a tight non-L1 positive-excess source certificate
-- statement:
--   Given a two-scale family of original centred physical-grid corrections and two separate nonnegative positive-part budgets for smooth interior cells and the true ruin-contact cell, with a vanishing outer tolerance η(n), a suitable inner localisation yields a small expected exact positive payoff deficit. This bridge places no integrability assumption on the original signed generator/drift source B.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_positive_errors_exact_excess_without_B_L1
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_two_scale_positive_excess_of_cell_and_contact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F B : ℕ → Ω → ℝ) (base : ℝ)
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ)
    (hηpos : ∀ n, 0 < η n)
    (hηzero : Tendsto η atTop (nhds (0 : ℝ)))
    (hM : ∀ n k, Integrable (M n k) P ∧
      (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable
      (fun ω => max (ErrCell n k ω) 0) P)
    (hContact : ∀ n k, Integrable
      (fun ω => max (ErrContact n k ω) 0) P)
    (hExcessMeas : ∀ n k, AEStronglyMeasurable
      (fun ω => max (F n ω - (base + (M n k ω + B n ω))) 0) P)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hPick : ∀ n (ε : ℝ), 0 < ε →
      ∃ k : ℕ,
        (∫ ω, max (ErrCell n k ω) 0 ∂P) +
          (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    ∃ (M' : ℕ → ℕ → Ω → ℝ) (η' : ℕ → ℝ),
      (∀ n, 0 < η' n) ∧
      Tendsto η' atTop (nhds (0 : ℝ)) ∧
      (∀ n k, Integrable (M' n k) P ∧
        (∫ ω, M' n k ω ∂P) = 0) ∧
      (∀ n k, Integrable (fun ω =>
        max (F n ω - (base + (M' n k ω + B n ω))) 0) P) ∧
      (∀ n (ε : ℝ), 0 < ε →
        ∃ k : ℕ,
          (∫ ω,
            max (F n ω - (base + (M' n k ω + B n ω))) 0 ∂P)
            ≤ η' n + ε) := by sorry
