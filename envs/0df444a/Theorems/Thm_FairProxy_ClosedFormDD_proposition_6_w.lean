-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_proposition_6_w
-- name    : FairProxy.ClosedFormDD.proposition_6_w
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:01.109132+00:00
-- url     : https://prove2.me/theorems/8e60ba32-3d7c-41c3-9ee4-917f1fc888ef
-- title:
--   Proposition 6, p. 14 — constraints on attainable demographic-disparity weights
-- statement:
--   Fix valid marginals of $A$ and $(\hat Y,Y)$ conditional on $Z$. A measurable class-weight function $w$ belongs to $\mathcal W(\mathcal P_D)$ exactly when it satisfies the law of total probability and, on every decision cell of positive conditional probability, is a probability vector across the two classes:
--
--   $$
--   \sum_{\hat y}w_\alpha(\hat y,z)P(\hat Y=\hat y\mid Z=z)=P(A=\alpha\mid Z=z),
--   \qquad
--   \sum_\alpha w_\alpha(\hat y,z)=1,
--   \qquad 0\le w_\alpha(\hat y,z)\le1.
--   $$
--
--   This is the $\mathcal W$ part of Proposition 6, characterizing which conditional class weights can arise from a compatible joint.
--
--   **Formalization Note** The first equality holds at every $z$. The last two constraints apply only when $P(\hat Y=\hat y\mid Z=z)>0$, since a conditional class probability on a null cell is undefined. The paper also gives a separate $\widetilde{\mathcal W}$ statement for other disparities.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 14, Proposition 6, W part; Appendix B.3, p. 50

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Model

namespace FairProxy.ClosedFormDD

/-- Proposition 6, p. 14, for the DD weights, with conditional probabilities constrained
only on positive-probability decision cells. -/
theorem proposition_6_w {Z : Type*} [MeasurableSpace Z]
    (M : Marginals Z) (hM : M.Valid) :
    WPD M =
      {w | (∀ α ŷ, Measurable (w α ŷ)) ∧
           (∀ α z, ∑ ŷ, w α ŷ z * etaPri M ŷ z = M.etaAux α z) ∧
           ∀ ŷ z, 0 < etaPri M ŷ z →
             (∑ α, w α ŷ z = 1) ∧
               ∀ α, 0 ≤ w α ŷ z ∧ w α ŷ z ≤ 1} := by sorry

end FairProxy.ClosedFormDD
