-- Prove2me | Theorems.Thm_ConformalRiskControl_monotonized_risk_control
-- name    : ConformalRiskControl.monotonized_risk_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:15:28.781034+00:00
-- url     : https://prove2.me/theorems/d46ca6b8-db24-4981-80f1-5c6e556efbbb
-- title:
--   Corollary 1: conformal risk control with monotonized losses
-- statement:
--   Let $\Lambda\subset\mathbb{R}$ be nonempty and compact with $\lambda_{\max}=\max\Lambda$, let $n\ge1$ and $\alpha<B$. Let $L_1,\dots,L_{n+1}$ be an exchangeable collection of random functions on $\Lambda$ with right-continuous, possibly non-monotone, realisations. Assume that almost surely $L_i(\lambda_{\max})\le\alpha$ and $\sup_\lambda L_i(\lambda)\le B$ for every $i$. Set
--   $$\tilde L_i(\lambda)=\sup_{\lambda'\ge\lambda}L_i(\lambda'),\qquad\tilde R_n=\frac1n\sum_{i=1}^n\tilde L_i,\qquad\tilde\lambda=\inf\Big\{\lambda:\tfrac{n}{n+1}\tilde R_n(\lambda)+\tfrac{B}{n+1}\le\alpha\Big\}.$$
--   Then
--   $$\mathbb{E}\big[L_{n+1}(\tilde\lambda)\big]\le\alpha.$$
--
--   **Formalization Note** The corollary says "any (possibly non-monotone) function satisfying (5)". The losses are kept right-continuous and exchangeable, as in Theorem 1, from which the corollary is derived. Without right-continuity the claim fails. For example, take $L_i(\lambda)=\mathbb{1}\{\lambda\le1/2\}$ on $[0,1]$ with $n=1$, $B=1$, $\alpha=1/2$. These losses are monotone, so $\tilde L_i=L_i$; then $\tilde\lambda=1/2$ and $L_2(\tilde\lambda)=1$.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 2.4, Corollary 1, p. 5

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem monotonized_risk_control {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (Λ : Set ℝ) (hΛ : IsCompact Λ)
    (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B) (L : Fin (n + 1) → Ω → ℝ → ℝ)
    (hexch : IsExchangeable P Λ L) (hrc : ∀ i ω, IsRightContOn Λ (L i ω))
    (h5 : ∀ᵐ ω ∂P, ∀ i, LossBounds Λ B α (L i ω)) :
    upperExp P B (fun ω =>
        L (Fin.last n) ω (lhat Λ B α (fun i : Fin n => supRight Λ (L i.castSucc ω))))
      ≤ (α : EReal) := by sorry

end ConformalRiskControl
