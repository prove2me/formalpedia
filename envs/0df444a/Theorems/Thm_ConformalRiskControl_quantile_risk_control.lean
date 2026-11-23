-- Prove2me | Theorems.Thm_ConformalRiskControl_quantile_risk_control
-- name    : ConformalRiskControl.quantile_risk_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:17:38.116936+00:00
-- url     : https://prove2.me/theorems/db1167b7-84c4-4286-a1a4-7216d78862fb
-- title:
--   Proposition 4: quantile risk control
-- statement:
--   Let $\Lambda\subset\mathbb{R}$ be nonempty and compact with $\lambda_{\max}=\max\Lambda$, let $n\ge1$, $\alpha<B$ and $\beta\in(0,1]$. Let $L_1,\dots,L_{n+1}$ be as in Theorem 1: exchangeable, with non-increasing, right-continuous realisations, and almost surely $L_i(\lambda_{\max})\le\alpha$ and $\sup_\lambda L_i(\lambda)\le B$. With
--   $$\hat\lambda_\beta=\inf\Big\{\lambda\in\Lambda:\frac1{n+1}\sum_{i=1}^n\mathbb{1}\{L_i(\lambda)>\alpha\}+\frac1{n+1}\le1-\beta\Big\},$$
--   the $\beta$-quantile of the test loss satisfies
--   $$\mathrm{Quantile}_\beta\big(L_{n+1}(\hat\lambda_\beta)\big)\le\alpha,$$
--   where $\mathrm{Quantile}_\beta(X)=\inf\{x:\mathbb{P}(X\le x)\ge\beta\}$.
--
--   **Formalization Note** The paper does not state the range of $\beta$. It is taken to be $(0,1]$, where the quantile is a finite real number.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 4.2, Proposition 4, eq. (11), p. 11; proof in Appendix B, p. 19

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem quantile_risk_control {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (Λ : Set ℝ) (hΛ : IsCompact Λ)
    (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B) (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β ≤ 1)
    (L : Fin (n + 1) → Ω → ℝ → ℝ)
    (hexch : IsExchangeable P Λ L) (hanti : ∀ i ω, AntitoneOn (L i ω) Λ)
    (hrc : ∀ i ω, IsRightContOn Λ (L i ω)) (h5 : ∀ᵐ ω ∂P, ∀ i, LossBounds Λ B α (L i ω)) :
    quantile P (fun ω =>
        L (Fin.last n) ω (lhatQuantile Λ α β (fun i : Fin n => L i.castSucc ω))) β ≤ α := by sorry

end ConformalRiskControl
