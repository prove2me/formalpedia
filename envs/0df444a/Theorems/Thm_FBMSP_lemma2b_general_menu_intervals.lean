-- Prove2me | Theorems.Thm_FBMSP_lemma2b_general_menu_intervals
-- name    : FBMSP.lemma2b_general_menu_intervals
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:55:54.417201+00:00
-- url     : https://prove2.me/theorems/505ae92f-135c-434b-86cf-4b280fe76925
-- title:
--   Lemma 2(b) — Interval assignment for arbitrary prediction values
-- statement:
--   Fix a nonempty, nondecreasing list of nonnegative prices and an integrable mean-zero MHR error law. There exists a nondecreasing assignment of every real prediction value to a menu index that maximizes the pointwise expected revenue. Each nonempty assignment fiber is an interval: if two ordered endpoints receive the same index, all prediction values between them receive that index too.
--
--   This fixed-menu statement retains arbitrary prediction values and therefore supports both atomic and continuous prediction laws. It asserts existence of a suitable interval assignment; ties need not make every optimal assignment interval.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Lemma 2(b), p.17; proof pp.42–43 (ec8–ec9).

import Definitions.Def_FBMSP_Model

namespace FBMSP

theorem lemma2b_general_menu_intervals {k : ℕ}
    (hk : 0 < k) (η : MeasureTheory.Measure ℝ)
    (hη : ValidNoise η) (hMHR : HasMHR η)
    (p : Fin k → ℝ) (hp : Monotone p) (hpNonneg : ∀ j, 0 ≤ p j) :
    ∃ a : ℝ → Fin k, Monotone a ∧
      (∀ (x : ℝ) (j : Fin k), postedRevenue η x (p j) ≤
        postedRevenue η x (p (a x))) ∧
      (∀ x₁ x₂ x₃ : ℝ, x₁ ≤ x₂ → x₂ ≤ x₃ →
        a x₁ = a x₃ → a x₂ = a x₁) := by sorry

end FBMSP
