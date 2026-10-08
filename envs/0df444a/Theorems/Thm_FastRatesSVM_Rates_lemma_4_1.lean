-- Prove2me | Theorems.Thm_FastRatesSVM_Rates_lemma_4_1
-- name    : FastRatesSVM.Rates.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:46.63306+00:00
-- url     : https://prove2.me/theorems/5cf8fc01-7a84-4511-841b-75bfcf54ff04
-- title:
--   Lemma 4.1 — boundary-distance balls remain in their enlarged class
-- statement:
--   For the closed unit ball $X\subseteq\mathbb R^d$, let $\widetilde\eta$ be the radial extension in (23), and let $\widetilde X_1,\widetilde X_{-1}$ be its positive and negative classes in $3X$. Then
--   $$
--   x\in X_1\Longrightarrow B(x,\tau_x)\subseteq\widetilde X_1,\qquad
--   x\in X_{-1}\Longrightarrow B(x,\tau_x)\subseteq\widetilde X_{-1}.
--   $$
--
--   This geometric fact supports the Gaussian approximation estimate. **Formalization Note** Distance to an empty opposite-class set is zero; then the corresponding open ball is empty.
-- source:
--   Steinwart, Scovel, Fast Rates for Support Vector Machines Using Gaussian Kernels, arXiv:0708.1838v1, p. 15, Lemma 4.1

import Definitions.Def_FastRatesSVM_Rates_Extension

namespace FastRatesSVM.Rates

/-- Lemma 4.1, arXiv:0708.1838v1, p. 15. -/
theorem lemma_4_1 (d : ℕ) (hd : 0 < d) (D : BinaryDistribution d) :
    (∀ x ∈ Xplus D, Metric.ball x (tau D x) ⊆ extendedPlus D) ∧
    (∀ x ∈ Xminus D, Metric.ball x (tau D x) ⊆ extendedMinus D) := by sorry

end FastRatesSVM.Rates
