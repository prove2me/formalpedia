-- Prove2me | Theorems.Thm_DRJointCC_Joint_eq_7
-- name    : DRJointCC.Joint.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:33:41.021723+00:00
-- url     : https://prove2.me/theorems/10bcd215-b402-4c5e-a9cc-df07bd3c2200
-- title:
--   (7), p. 6 — sup_P P-CVaR_ε(L) ≤ 0 implies inf_P P(L ≤ 0) ≥ 1 − ε, for every measurable loss L
-- statement:
--   Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, let $\epsilon\in(0,1)$, and let $L:\mathbb R^k\to\mathbb R$ be a measurable loss function. If the worst-case CVaR of $L$ is nonpositive, then the distributionally robust chance constraint holds:
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\big(L(\tilde\xi)\big)\le0\ \Longrightarrow\ \inf_{\mathbb P\in\mathcal P}\mathbb P\big(L(\tilde\xi)\le0\big)\ge1-\epsilon.
--   $$
--
--   This is the conservativeness of the worst-case CVaR approximation. The paper derives it from $\mathbb P(L(\tilde\xi)\le\mathbb P\text{-}\mathrm{CVaR}_\epsilon(L(\tilde\xi)))\ge1-\epsilon$, which holds for every distribution and every measurable loss; in §3 it is applied to the scaled max-loss of the joint constraint.
--
--   **Formalization Note** The display (7) is printed for the affine loss $y^0(x)+y(x)^\top\tilde\xi$, while the sentence before it states the implication for every probability distribution and loss function; the theorem takes that generality, which is what (29) needs. CVaR is extended-real valued (see the definitions). The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ of §2 are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 6, (7) and the sentence preceding it

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- (7), p. 6, for every measurable loss: if the worst-case CVaR of `L` over the moment set is
nonpositive, then `inf_{ℙ ∈ 𝒫} ℙ(L(ξ̃) ≤ 0) ≥ 1 − ε`. -/
theorem eq_7 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L) :
    DRJointCC.Individual.wcCVaR ε μ Sig L ≤ 0 →
      ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ DRJointCC.Individual.ambiguitySet μ Sig, P {ξ | L ξ ≤ 0} := by sorry

end DRJointCC.Joint
