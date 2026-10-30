-- Prove2me | Theorems.Thm_FBMSP_lemma2b_finite_menu_intervals
-- name    : FBMSP.lemma2b_finite_menu_intervals
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T04:56:27.430428+00:00
-- url     : https://prove2.me/theorems/da7799cc-60dc-4e64-836c-a35bf9df5dbd
-- title:
--   Lemma 2(b) — Finite-menu interval domination
-- statement:
--   For a finite sorted prediction support with positive probability weights, a nonempty sorted nonnegative price menu, and independent integrable mean-zero MHR error, there exists a monotone maximizing assignment with interval fibers. It weakly improves revenue relative to every other assignment using that menu.
--
--   Repeated prices, unused menu indices, zero purchase probabilities, and ties are allowed. This is the finite computational specialization used by Theorem 2.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Lemma 2(b), p.17; proof pp.42–43 (ec8–ec9); finite regime of Theorem 2.

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Tie-safe finite-menu form of Lemma 2(b): there exists a monotone row
maximizer, whose fibers are intervals and whose expected revenue dominates
every assignment using that same menu.  Draft statement; proof remains open. -/
theorem lemma2b_finite_menu_intervals {n k : ℕ}
    (η : MeasureTheory.Measure ℝ) (hnoise : ValidNoise η) (hmhr : HasMHR η)
    (μ w : Fin n → ℝ) (hmarket : ValidFiniteMarket μ w)
    (hk : 0 < k) (p : Fin k → ℝ)
    (hp : Monotone p) (hp_nonneg : ∀ j, 0 ≤ p j) :
    ∃ a : Fin n → Fin k,
      Monotone a ∧
      (∀ i j, postedRevenue η (μ i) (p j) ≤
        postedRevenue η (μ i) (p (a i))) ∧
      (∀ i₁ i₂ i₃, i₁ ≤ i₂ → i₂ ≤ i₃ →
        a i₁ = a i₃ → a i₂ = a i₁) ∧
      ∀ b : Fin n → Fin k,
        finitePolicyRevenue η μ w b p ≤ finitePolicyRevenue η μ w a p := by sorry

end FBMSP
