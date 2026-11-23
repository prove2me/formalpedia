-- Prove2me | Theorems.Thm_ConformalRiskControl_u_risk_control
-- name    : ConformalRiskControl.u_risk_control
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:18:16.784195+00:00
-- url     : https://prove2.me/theorems/611c215a-b98f-41d3-8c0d-bfc534467490
-- title:
--   Proposition 7: U-risk control
-- statement:
--   Let $1<k\le n$, let $\Lambda\subset\mathbb{R}$ be nonempty and compact with $\lambda_{\max}=\max\Lambda$, and let $\alpha<B$. For every $k$-subset $S\subset\{1,\dots,n+k\}$ let $L_S$ be a random function on $\Lambda$. Assume the family $(L_S)$ is exchangeable under relabelling of $\{1,\dots,n+k\}$. Assume every realisation of every $L_S$ is non-increasing and right-continuous, and that almost surely
--   $$L_S(\lambda_{\max})\le\alpha,\qquad\sup_\lambda L_S(\lambda)\le B\quad\text{for all }S.$$
--   Then the parameter $\hat\lambda_k$ of eq. (16) satisfies
--   $$\mathbb{E}\big[L_{\{n+1,\dots,n+k\}}(\hat\lambda_k)\big]\le\alpha.$$
--
--   This extends Theorem 1 to risks that are expectations of order-$k$ U-statistics, as in ranking and metric learning.
--
--   **Formalization Note** Proposition 7 does not state exchangeability, but its proof uses it ("the same argument as in the end of the proof of Theorem 1"), and without it the claim fails. The condition $k\le n$ is the range in which the factor $(n-k)!$ of eq. (16) is defined.
-- source:
--   Angelopoulos, Bates, Fisch, Lei and Schuster, Conformal Risk Control, arXiv:2208.02814v4, Section 4.5, Proposition 7, eqs. (15)-(16), p. 12; proof in Appendix B, p. 19

import Mathlib
import Definitions.Def_ConformalRiskControl_Basic

open MeasureTheory ProbabilityTheory Filter

namespace ConformalRiskControl

theorem u_risk_control {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n k : ℕ) (hk : 1 < k) (hkn : k ≤ n) (Λ : Set ℝ)
    (hΛ : IsCompact Λ) (hΛne : Λ.Nonempty) (B α : ℝ) (hαB : α < B)
    (L : Finset (Fin (n + k)) → Ω → ℝ → ℝ) (hexch : IsExchangeableU P Λ n k L)
    (hanti : ∀ S : Finset (Fin (n + k)), S.card = k → ∀ ω, AntitoneOn (L S ω) Λ)
    (hrc : ∀ S : Finset (Fin (n + k)), S.card = k → ∀ ω, IsRightContOn Λ (L S ω))
    (h5 : ∀ᵐ ω ∂P, ∀ S : Finset (Fin (n + k)), S.card = k → LossBounds Λ B α (L S ω)) :
    upperExp P B (fun ω => L (testSubset n k) ω (lhatU Λ B α n k (fun S => L S ω)))
      ≤ (α : EReal) := by sorry

end ConformalRiskControl
