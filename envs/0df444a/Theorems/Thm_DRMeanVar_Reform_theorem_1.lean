-- Prove2me | Theorems.Thm_DRMeanVar_Reform_theorem_1
-- name    : DRMeanVar.Reform.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:15.031989+00:00
-- url     : https://prove2.me/theorems/05f5e4a4-c985-4bf0-b119-fdd242d9f24a
-- title:
--   Theorem 1, p. 6 — robust mean-variance selection equals penalized empirical variance minimization
-- statement:
--   Let $R_1,\ldots,R_n\in\mathbb R^d$ be observed returns, $n\ge1$, $\delta\ge0$, and let $p,q$ be conjugate exponents with $1\le q<\infty$. The feasible set $F_{\delta,\bar\alpha}(n)$ requires portfolio weights summing to one and worst-case expected return at least $\bar\alpha$ over the squared-$\ell_q$ Wasserstein ball $U_\delta(P_n)$. Then problem (2) and problem (9) have the same optimal portfolios and the same optimal value:
--   $$\min_{\varphi\in F_{\delta,\bar\alpha}(n)}\sup_{P\in U_\delta(P_n)}\operatorname{Var}_P(\varphi^TR)
--     =\min_{\varphi\in F_{\delta,\bar\alpha}(n)}\left(\sqrt{\operatorname{Var}_{P_n}(\varphi^TR)}+\sqrt\delta\,\|\varphi\|_p\right)^2.$$
--
--   The result expresses the distributionally robust portfolio problem as empirical variance minimization with a norm penalty.
--
--   **Formalization Note** The objective of (2) is an extended-real supremum, and the statement separately equates minimizer sets and infimum values; it does not assume a feasible or optimal portfolio exists. The sample size, nonnegative radius, and finite $q$ are the standing conventions of §2.1. The $q=1$, $p=\infty$ endpoint is included.
-- source:
--   Blanchet, Chen & Zhou, Distributionally Robust Mean-Variance Portfolio Selection with Wasserstein Distances, arXiv:1802.04885v1, p. 6, Theorem 1, (9)

import Mathlib
import Definitions.Def_DRMeanVar_Reform_Setting

open MeasureTheory

namespace DRMeanVar.Reform

/-- Theorem 1, p. 6: (2) and (9) have the same optimal portfolios and value. -/
theorem theorem_1 {d n : ℕ} [NeZero n]
    (R : Fin n → (Fin d → ℝ)) (q p : ENNReal) (δ αbar : ℝ)
    (hδ : 0 ≤ δ) (hq : 1 ≤ q) (hqtop : q ≠ ⊤)
    (hpq : p.HolderConjugate q) :
    (∀ φ : Fin d → ℝ,
      (φ ∈ F q δ αbar R ∧ IsMinOn (robustObj q δ R) (F q δ αbar R) φ) ↔
      (φ ∈ F q δ αbar R ∧
        IsMinOn (fun ψ => (dualObj p δ R ψ : EReal)) (F q δ αbar R) φ)) ∧
    (⨅ φ ∈ F q δ αbar R, robustObj q δ R φ) =
      (⨅ φ ∈ F q δ αbar R, (dualObj p δ R φ : EReal)) := by sorry

end DRMeanVar.Reform
