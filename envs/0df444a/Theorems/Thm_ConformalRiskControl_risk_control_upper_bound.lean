-- Prove2me | Theorems.Thm_ConformalRiskControl_risk_control_upper_bound
-- name    : ConformalRiskControl.risk_control_upper_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:13:13.581797+00:00
-- url     : https://prove2.me/theorems/785acee8-50e2-4fa1-8b83-5b711009bbc2
-- title:
--   Theorem 1: conformal risk control
-- statement:
--   Let $\Lambda\subset\mathbb{R}$ be nonempty and compact, with $\lambda_{\max}=\max\Lambda$, let $n\ge1$, and let $\alpha<B$ be real numbers. Let $L_1,\dots,L_{n+1}:\Lambda\to\mathbb{R}$ be an exchangeable collection of random functions. Assume that every realisation of each $L_i$ is non-increasing and right-continuous on $\Lambda$, and that almost surely, for every $i$,
--   $$L_i(\lambda_{\max})\le\alpha,\qquad\sup_{\lambda\in\Lambda}L_i(\lambda)\le B.$$
--   Let $\hat\lambda$ be the conformal risk control parameter (eq. 4) computed from $L_1,\dots,L_n$. Then
--   $$\mathbb{E}\big[L_{n+1}(\hat\lambda)\big]\le\alpha.$$
--
--   This is the main guarantee of the paper. It extends the coverage guarantee of split conformal prediction to the expected value of any bounded monotone loss.
--
--   **Formalization Note** The losses are bounded above but not below, so the expectation is taken in $[-\infty,B]$ as $B-\mathbb{E}[B-L_{n+1}(\hat\lambda)]$. The paper does not specify $\Lambda$ beyond $\sup\Lambda\in\Lambda$. Compactness is the assumption under which $\hat\lambda\in\Lambda$, so that $L_{n+1}(\hat\lambda)$ is defined.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 2.1, Theorem 1, eqs. (3)-(5), p. 3 (setting: Section 1.1, eq. (4), p. 2; proof pp. 3-4)

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem risk_control_upper_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (Λ : Set ℝ) (hΛ : IsCompact Λ)
    (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B) (L : Fin (n + 1) → Ω → ℝ → ℝ)
    (hexch : IsExchangeable P Λ L) (hanti : ∀ i ω, AntitoneOn (L i ω) Λ)
    (hrc : ∀ i ω, IsRightContOn Λ (L i ω)) (h5 : ∀ᵐ ω ∂P, ∀ i, LossBounds Λ B α (L i ω)) :
    upperExp P B (fun ω => L (Fin.last n) ω (lhat Λ B α (fun i : Fin n => L i.castSucc ω)))
      ≤ (α : EReal) := by sorry

end ConformalRiskControl
