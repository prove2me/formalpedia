-- Prove2me | Theorems.Thm_EquivPosMaps_TwoPositive_proposition_3_3
-- name    : EquivPosMaps.TwoPositive.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:26:54.812989+00:00
-- url     : https://prove2.me/theorems/1044d732-4880-4cc4-beae-cbd8f369ef80
-- title:
--   Proposition 3.3: complete positivity and copositivity
-- statement:
--   For real $\alpha,\beta$, put $\Phi[\alpha,\beta]=\Phi_{\alpha,\beta,3}$ and $\ell_{CP}(\beta)=[-(3+3\beta)+\sqrt{9\beta^2-10\beta+17}]/2$. Complete positivity and complete copositivity coincide for this family. They hold exactly when the applicable parameter conditions hold:
--
--   $$
--   \beta\leq-\tfrac15\Longrightarrow\alpha\geq\ell_{CP}(\beta),\qquad
--   \beta\geq-\tfrac15\Longrightarrow\bigl(\alpha\geq\ell_{CP}(\beta)\text{ and }\alpha\geq1\bigr).
--   $$
--
--   Both conditions apply at $\beta=-1/5$ and agree there. This gives the complete positivity boundary used to separate the target region.
-- source:
--   Collins, Osaka & Sapra, On a family of a linear maps from Mn(C) to Mn2(C), arXiv:1802.07553v1, pp. 7–8, Proposition 3.3

import Mathlib
import Definitions.Def_EquivPosMaps_TwoPositive_Basic
open scoped Matrix Kronecker ComplexOrder
noncomputable section

namespace EquivPosMaps.TwoPositive
/-- Proposition 3.3, pp. 7–8: complete positivity and complete copositivity of Φ[α,β]. -/
theorem proposition_3_3 (α β : ℝ) :
    (QAlgorithms.Entanglement.IsCompletelyPositive (phi 3 α β) ↔
      IsCompletelyCopositive (phi 3 α β)) ∧
    (QAlgorithms.Entanglement.IsCompletelyPositive (phi 3 α β) ↔
      ((β ≤ -1/5 → lowCP β ≤ α) ∧
        (-1/5 ≤ β → lowCP β ≤ α ∧ 1 ≤ α))) := by sorry

end EquivPosMaps.TwoPositive
