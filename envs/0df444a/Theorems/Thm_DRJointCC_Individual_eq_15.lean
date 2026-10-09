-- Prove2me | Theorems.Thm_DRJointCC_Individual_eq_15
-- name    : DRJointCC.Individual.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:25.342085+00:00
-- url     : https://prove2.me/theorems/ed00095c-178b-41af-84e0-8d272c3ccd7d
-- title:
--   (15), p. 8 — the robust chance constraint holds iff the worst-case VaR is ≤ 0
-- statement:
--   Let $\mathcal P$ be the set of probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance $\Sigma\succ0$, let $\epsilon\in(0,1)$, and let $L:\mathbb R^k\to\mathbb R$ be a measurable loss function. Then
--
--   $$
--   \inf_{\mathbb P\in\mathcal P}\mathbb P\big(L(\tilde\xi)\le0\big)\ge1-\epsilon\iff\mathrm{WC\text{-}VaR}_\epsilon\big(L(\tilde\xi)\big)\le0,
--   $$
--
--   where $\mathrm{WC\text{-}VaR}_\epsilon(L(\tilde\xi))=\inf\{\gamma\in\mathbb R:\inf_{\mathbb P\in\mathcal P}\mathbb P(L(\tilde\xi)\le\gamma)\ge1-\epsilon\}$ is the worst-case Value-at-Risk (14).
--
--   This is the first step of the proof of Theorem 2.2: it reduces the distributionally robust chance constraint to a sign condition on the worst-case VaR.
--
--   **Formalization Note** The paper states (15) inside the proof of Theorem 2.2, for a continuous concave or quadratic loss; its argument uses only measurability of $L$, so the statement is made for every measurable $L$, which is stronger. The worst-case VaR is extended-real valued. The standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ of §2 are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 8, (15) (proof of Theorem 2.2)

import Mathlib
import Definitions.Def_DRJointCC_Individual_Individual

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual

/-- (15), p. 8: under the standing assumptions, the distributionally robust individual chance
constraint holds iff the worst-case VaR (14) is nonpositive, for every measurable loss `L`. -/
theorem eq_15 {k : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : (Fin k → ℝ) → ℝ) (hL : Measurable L) :
    ENNReal.ofReal (1 - ε) ≤ ⨅ P ∈ ambiguitySet μ Sig, P {ξ | L ξ ≤ 0} ↔
      wcVaR ε μ Sig L ≤ 0 := by sorry

end DRJointCC.Individual
