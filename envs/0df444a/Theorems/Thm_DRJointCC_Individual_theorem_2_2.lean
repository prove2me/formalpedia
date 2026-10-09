-- Prove2me | Theorems.Thm_DRJointCC_Individual_theorem_2_2
-- name    : DRJointCC.Individual.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:33.540444+00:00
-- url     : https://prove2.me/theorems/5356ec9e-8a53-47c3-ae71-a726c6878bf7
-- title:
--   Theorem 2.2, p. 8 — for continuous concave or quadratic L, worst-case CVaR ≤ 0 iff inf_P P(L ≤ 0) ≥ 1 − ε
-- statement:
--   Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^k$ with mean vector $\mu$ and covariance matrix $\Sigma\succ0$, and let $\epsilon\in(0,1)$. Let $L:\mathbb R^k\to\mathbb R$ be a continuous loss function that is either
--
--   1. concave in $\xi$, or
--   2. (possibly nonconcave) quadratic in $\xi$.
--
--   Then the following equivalence holds:
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(L(\tilde\xi)\big)\le0\iff\inf_{\mathbb P\in\mathcal P}\mathbb P\big(L(\tilde\xi)\le0\big)\ge1-\epsilon. \tag{13}
--   $$
--
--   Here $\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi))=\inf_{\beta}\{\beta+\frac1\epsilon\mathbb E_{\mathbb P}((L(\tilde\xi)-\beta)^+)\}$. The implication from left to right holds for every loss; the theorem says that for these two classes of losses the worst-case CVaR constraint, which is a tractable conservative approximation of the distributionally robust chance constraint, is in fact exact.
--
--   **Formalization Note** The worst-case CVaR is extended-real valued, so a loss with infinite CVaR under some $\mathbb P\in\mathcal P$ is not mapped to a junk value. $\mathcal P$ consists of all probability measures with finite second moments and the given mean and covariance. A quadratic loss is $\xi^\top Q\xi+q^\top\xi+q^0$ with no definiteness or symmetry imposed on $Q$; concavity is on all of $\mathbb R^k$. The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ of §2 are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 8, Theorem 2.2, (13)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- Theorem 2.2, p. 8: for a continuous loss `L` that is concave or (possibly nonconcave)
quadratic, the worst-case CVaR constraint is equivalent to the distributionally robust
individual chance constraint (13). -/
theorem theorem_2_2 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (hSig : Sig.PosDef) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Continuous L)
    (hshape : ConcaveOn ℝ Set.univ L ∨ IsQuadratic L) :
    wcCVaR ε μ Sig L ≤ 0 ↔
      ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ 0} := by sorry

end DRJointCC.Individual
