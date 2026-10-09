-- Prove2me | Theorems.Thm_DRJointCC_Individual_wcCVaR_eq_sdp
-- name    : DRJointCC.Individual.wcCVaR_eq_sdp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:28.574832+00:00
-- url     : https://prove2.me/theorems/af4219b6-e843-4b3d-85c2-48ed7628922c
-- title:
--   p. 10, display after (20) — for concave or quadratic L, the worst-case CVaR equals the interchanged form (9) and the value of (20)
-- statement:
--   Let $\mathcal P$ be the set of probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, $\Omega$ the second-order moment matrix, and $\epsilon\in(0,1)$. Let $L:\mathbb R^k\to\mathbb R$ be a continuous loss function that is either concave or (possibly nonconcave) quadratic in $\xi$. Then
--
--   1. the supremum over $\mathcal P$ and the infimum over $\beta$ may be interchanged:
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi))=\inf_{\beta\in\mathbb R}\Big\{\beta+\frac1\epsilon\sup_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}\big((L(\tilde\xi)-\beta)^+\big)\Big\};
--   $$
--   2. the worst-case CVaR is the optimal value of the semidefinite program (20):
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi))=\inf\Big\{\beta+\frac1\epsilon\langle\Omega,M\rangle:\ M\in\mathbb S^{k+1},\ \beta\in\mathbb R,\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top+\beta-L(\xi)\ge0\ \ \forall\xi\in\mathbb R^k\Big\}.
--   $$
--
--   This is the last step of the proof of Theorem 2.2: the worst-case CVaR has the same semidefinite representation as the worst-case VaR.
--
--   **Formalization Note** All quantities are extended reals. Part 1 is the interchange (9) of p. 6, which the paper justifies by a stochastic saddle-point theorem; it is stated only for the losses of Theorem 2.2, as used on p. 10. The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 10, display following (20) (proof of Theorem 2.2); p. 6, (9)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- The display after (20), p. 10: for a continuous loss that is concave or quadratic,
(a) the worst-case CVaR equals `inf_β { β + (1/ε) sup_{ℙ ∈ 𝒫} E_ℙ((L(ξ̃) − β)⁺) }` (the
interchange (9)), and (b) it equals the optimal value of the SDP (20). -/
theorem wcCVaR_eq_sdp {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Continuous L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ IsQuadratic L) :
    wcCVaR ε μ Sig L =
        ⨅ β : ℝ, ((β : EReal) + ((ε⁻¹ : ℝ) : EReal) * wcExpPos μ Sig (fun ξ => L ξ - β)) ∧
      wcCVaR ε μ Sig L = sdpValue20 ε μ Sig L := by sorry

end DRJointCC.Individual
