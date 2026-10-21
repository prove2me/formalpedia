-- Prove2me | Theorems.Thm_FlexGroupBuy_REE_Nbar_order
-- name    : FlexGroupBuy.REE.Nbar_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:48.243432+00:00
-- url     : https://prove2.me/theorems/61ad6ece-a268-486c-9d32-3e55ec160f7c
-- title:
--   Proof of Proposition 2, Online Appendix p. 4 — N̄2 > N̄1 if and only if H/L > 1/γ
-- statement:
--   Under the standing assumptions,
--   $$
--   \bar N_2>\bar N_1\iff \frac HL>\frac1\gamma,
--   $$
--   where $\bar N_1=(\theta-1)(1-\gamma)L\lambda/c+1-\gamma$ and $\bar N_2=(\theta-1)(H-L)\gamma\lambda/c+1-\gamma$.
--
--   This orders the two batch-size thresholds that govern the two cases of Proposition 2.
-- source:
--   Hu, Liu & Zhai, Intertemporal Segmentation via Flexible-Duration Group Buying, SSRN 3242687 (version of 2019-12-06; MSOM forthcoming), Online Appendix p. 4, proof of Proposition 2

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

namespace FlexGroupBuy.REE

/-- Proof of Proposition 2 (Online Appendix p. 4): `N̄2 > N̄1` if and only if `H/L > 1/γ`. -/
theorem Nbar_order (P : Params) (hP : P.Standing) :
    Nbar1 P < Nbar2 P ↔ 1 / P.gam < P.H / P.L := by sorry

end FlexGroupBuy.REE
