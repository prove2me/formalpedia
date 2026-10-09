-- Prove2me | Theorems.Thm_DRJointCC_Individual_wcCVaR_eq_wcVaR
-- name    : DRJointCC.Individual.wcCVaR_eq_wcVaR
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:11.174+00:00
-- url     : https://prove2.me/theorems/d1a9074d-f44b-4b01-953c-297053df1de6
-- title:
--   p. 9, first display — for concave or quadratic L, the worst-case CVaR equals the worst-case VaR
-- statement:
--   Let $\mathcal P$ be the set of probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, and let $\epsilon\in(0,1)$. Let $L:\mathbb R^k\to\mathbb R$ be a continuous loss function that is either concave or (possibly nonconcave) quadratic in $\xi$. Then
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(L(\tilde\xi)\big)=\mathrm{WC\text{-}VaR}_\epsilon\big(L(\tilde\xi)\big).
--   $$
--
--   The paper states that proving this identity suffices for Theorem 2.2, given (15).
--
--   **Formalization Note** Both sides are extended reals. The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 9, first display (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- p. 9, first display: for a continuous loss that is concave or quadratic, the worst-case
CVaR equals the worst-case VaR (14). -/
theorem wcCVaR_eq_wcVaR {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Continuous L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ IsQuadratic L) :
    wcCVaR ε μ Sig L = wcVaR ε μ Sig L := by sorry

end DRJointCC.Individual
