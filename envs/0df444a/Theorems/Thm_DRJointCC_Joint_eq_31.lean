-- Prove2me | Theorems.Thm_DRJointCC_Joint_eq_31
-- name    : DRJointCC.Joint.eq_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:25.169029+00:00
-- url     : https://prove2.me/theorems/927c07ff-ce9d-4eea-8b71-129e2730c37d
-- title:
--   (31), p. 16 — 𝒥(x, α) = inf_β {β + (1/ε) sup_P E_P[(max_i α_i(y_i^0(x) + y_i(x)ᵀξ) − β)⁺]}
-- statement:
--   Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma\succ0$, let $\epsilon\in(0,1)$, consider a joint chance constraint with $m\ge1$ affine constraint functions, fix a decision $x\in\mathbb R^n$ and strictly positive scaling parameters $\alpha$. Then the worst-case CVaR of the scaled max-loss equals
--   $$
--   \mathcal J(x,\alpha)=\sup_{\mathbb P\in\mathcal P}\mathrm{CVaR}_\epsilon\Big(\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\tilde\xi\big)\Big)=\inf_{\beta\in\mathbb R}\Big\{\beta+\frac1\epsilon\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}\Big(\Big[\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\tilde\xi\big)-\beta\Big]^+\Big)\Big\}.
--   $$
--
--   This interchange of the supremum over distributions with the infimum over $\beta$ is the first step of the semidefinite representation of $\mathcal Z^{\mathrm{JCC}}(\alpha)$ (Theorem 3.3).
--
--   **Formalization Note** All quantities are extended reals. The paper justifies the interchange, "as in Section 2", by a stochastic saddle-point theorem; the statement is made for the scaled max-loss only, as on the page. $m\ge1$, $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 16, proof of Theorem 3.3, (31)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- (31), p. 16: for `α ∈ 𝒜`, the worst-case CVaR `𝒥(x, α)` of the scaled max-loss equals
`inf_{β ∈ ℝ} { β + (1/ε) sup_{ℙ ∈ 𝒫} E_ℙ([max_i α_i (y_i^0(x) + y_i(x)ᵀξ̃) − β]⁺) }`. -/
theorem eq_31 {m n k : ℕ} (hm : 0 < m) (D : JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (x : Fin n → ℝ) (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    Jfun D μ Sig ε x α =
      ⨅ β : ℝ, ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) *
        DRJointCC.Individual.wcExpPos μ Sig (fun ξ => maxLoss D α x ξ - β)) := by sorry

end DRJointCC.Joint
