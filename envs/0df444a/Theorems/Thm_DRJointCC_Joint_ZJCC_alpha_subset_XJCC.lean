-- Prove2me | Theorems.Thm_DRJointCC_Joint_ZJCC_alpha_subset_XJCC
-- name    : DRJointCC.Joint.ZJCC_alpha_subset_XJCC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:32:03.017308+00:00
-- url     : https://prove2.me/theorems/b11be131-ed41-4c66-a274-7cb5e6701dff
-- title:
--   p. 17 (from (28)–(29), p. 15) — Z^JCC(α) ⊆ X^JCC for every α > 0
-- statement:
--   Let $\mathcal P$ be the moment set with mean $\mu$ and covariance $\Sigma\succ0$, let $\epsilon\in(0,1)$, and consider a joint chance constraint with $m\ge1$ affine constraint functions $y_i^0(x)+y_i(x)^\top\xi$. For every vector of strictly positive scaling parameters $\alpha$ ($\alpha_i>0$ for all $i$),
--   $$
--   \mathcal Z^{\mathrm{JCC}}(\alpha)\subseteq\mathcal X^{\mathrm{JCC}},
--   $$
--   where $\mathcal Z^{\mathrm{JCC}}(\alpha)$ is the set of decisions $x$ whose scaled max-loss $\max_i\alpha_i(y_i^0(x)+y_i(x)^\top\tilde\xi)$ has nonpositive worst-case CVaR, and $\mathcal X^{\mathrm{JCC}}$ is the feasible set of the distributionally robust joint chance constraint.
--
--   For a fixed choice of the scaling parameters the worst-case CVaR constraint is therefore a conservative approximation of the robust joint chance constraint. The argument on p. 15 rewrites the joint constraint as the individual constraint (28) on the scaled max-loss.
--
--   **Formalization Note** The scaling parameters are componentwise strictly positive, not merely nonzero and nonnegative. The hypothesis $m\ge1$ is implicit in the paper's maximum over $i=1,\dots,m$; the standing assumptions $\Sigma\succ0$ and $\epsilon\in(0,1)$ are hypotheses.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 17, first sentence after the proof of Theorem 3.3; p. 15, (28)–(29)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Joint

/-- p. 17 (from (28)–(29), p. 15): for every `α ∈ 𝒜`, `Z^JCC(α) ⊆ X^JCC`. -/
theorem ZJCC_alpha_subset_XJCC {m n k : ℕ} (hm : 0 < m) (D : JCCData m n k)
    (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ) (hSig : Sig.PosDef)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (α : Fin m → ℝ) (hα : ∀ i, 0 < α i) :
    ZJCCα D μ Sig ε α ⊆ XJCC D μ Sig ε := by sorry

end DRJointCC.Joint
