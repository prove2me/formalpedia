-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_xbar1_pos_iff
-- name    : FlexGroupBuy.REE.xbar1_pos_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:45.520622+00:00
-- url     : https://prove2.me/theorems/f950dc45-f8c0-4fea-a1e9-1f6340c9a900
-- title:
--   Proof of Proposition 2, Online Appendix p. 4 — x̄G1 > 0 if and only if N > N̄2
-- statement:
--   Under the standing assumptions and $N\ge1$,
--   $$
--   \bar x^G_1>0\iff N>\bar N_2,\qquad \bar N_2=\frac{(\theta-1)(H-L)\gamma\lambda}{c}+1-\gamma .
--   $$
--
--   So an interior switch point of the price exists exactly when the batch size exceeds $\bar N_2$.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 4, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 4): `x̄G1 > 0` if and only if `N > N̄2`. -/
theorem xbar1_pos_iff (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    0 < xbar1 P N ↔ Nbar2 P < N := by sorry

end FlexGroupBuy.REE
