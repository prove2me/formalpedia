-- Prove2me | Theorems.Thm_CrowdSignal_OnePrice_proposition_1
-- name    : CrowdSignal.OnePrice.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:03.561319+00:00
-- url     : https://prove2.me/theorems/f40f287c-6916-43ba-9779-a16a41da25e7
-- title:
--   Proposition 1: unique refined separating equilibrium
-- statement:
--   Consider the one-price crowdfunding game with $0<q_L<q_H$, $0<\alpha<1$, and financing target $T>0$. Define
--   $$\bar p_1=\frac{4q_H-(1-\alpha)q_L-\sqrt{(q_H-q_L)[16q_H-(1-\alpha)^2q_L]}}{8}.$$
--   When $T\le\bar p_1$, a separating equilibrium exists and survives the intuitive criterion with high-type funding price $p_H=\bar p_1$ and low-type price $p_L=(3+\alpha)q_L/8$. Every separating equilibrium that survives the criterion has exactly these two prices. When $\bar p_1<T<q_L$, no separating equilibrium exists.
--
--   The result identifies the funding-price distortion required for a credible high-quality signal when the entrepreneur cannot commit to the later regular-period price.
--
--   **Formalization Note** A separating equilibrium is defined by both types having no profitable feasible deviation under the paper's belief rule: the high type's on-path price signals high quality and all other prices signal low quality. The intuitive-criterion test uses strict inequalities for both types. The printed “otherwise, only a pooling equilibrium exists” is limited to $T<q_L$: for $T\ge q_L$ zero-profit separating profiles can exist, and pooling existence requires a prior absent from the main claim.
-- source:
--   Bolandifar, Chen, Kouvelis, Zhou, Quality Signaling through Crowdfunding Pricing, SSRN 3689946 (manuscript of 2022-05-30), p. 19, Proposition 1

import Mathlib
import Definitions.Def_CrowdSignal_OnePrice_Setting

namespace CrowdSignal.OnePrice

/-- Proposition 1: the unique refined separating equilibrium and its financing range. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    (P.T ≤ pbar P →
      IsSepEq P (pbar P) ((3 + P.α) / 8 * P.qL) ∧
      SurvivesIC P (pbar P) ((3 + P.α) / 8 * P.qL) ∧
      ∀ pH pL : ℝ, IsSepEq P pH pL → SurvivesIC P pH pL →
        pH = pbar P ∧ pL = (3 + P.α) / 8 * P.qL) ∧
    (pbar P < P.T → P.T < P.qL →
      ∀ pH pL : ℝ, ¬ IsSepEq P pH pL) := by sorry

end CrowdSignal.OnePrice
