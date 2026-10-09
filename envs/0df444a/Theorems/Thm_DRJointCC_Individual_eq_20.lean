-- Prove2me | Theorems.Thm_DRJointCC_Individual_eq_20
-- name    : DRJointCC.Individual.eq_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:19.19144+00:00
-- url     : https://prove2.me/theorems/a9bf541e-66cc-4f6c-ba7b-1aa9a1ce2a5d
-- title:
--   (20), p. 10 — for concave or quadratic L, the worst-case VaR equals the value of the SDP (20)
-- statement:
--   Let $\mathcal P$ be the set of probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, $\Omega$ the second-order moment matrix, and $\epsilon\in(0,1)$. Let $L:\mathbb R^k\to\mathbb R$ be a continuous loss function that is either concave or (possibly nonconcave) quadratic in $\xi$. Then the worst-case Value-at-Risk (14) is the optimal value of a semidefinite program:
--
--   $$
--   \mathrm{WC\text{-}VaR}_\epsilon(L(\tilde\xi))=\inf\Big\{\beta+\frac1\epsilon\langle\Omega,M\rangle:\ M\in\mathbb S^{k+1},\ \beta\in\mathbb R,\ M\succeq0,\ [\xi^\top\ 1]\,M\,[\xi^\top\ 1]^\top+\beta-L(\xi)\ge0\ \ \forall\xi\in\mathbb R^k\Big\}.
--   $$
--
--   Together with the identification of the worst-case CVaR with the same program, this shows that the worst-case CVaR and the worst-case VaR coincide, which is the core of Theorem 2.2.
--
--   **Formalization Note** Both sides are extended-real valued (an infeasible program has value $+\infty$). The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ of §2 and the hypotheses of Theorem 2.2 on $L$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 10, (20) (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- (20), p. 10: for a continuous loss that is concave or quadratic, the worst-case VaR (14)
equals the optimal value of the SDP (20). -/
theorem eq_20 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Continuous L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ IsQuadratic L) :
    wcVaR ε μ Sig L = sdpValue20 ε μ Sig L := by sorry

end DRJointCC.Individual
