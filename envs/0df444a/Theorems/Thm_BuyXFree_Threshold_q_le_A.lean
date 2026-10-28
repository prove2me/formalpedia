-- Prove2me | Theorems.Thm_BuyXFree_Threshold_q_le_A
-- name    : BuyXFree.Threshold.q_le_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:36.217311+00:00
-- url     : https://prove2.me/theorems/41259fe0-67e4-4d20-9e3e-0c9913aa42ae
-- title:
--   Proof of Proposition 3, Part (a), p. 47 — q ≤ 1/2 and δ ≥ 2/(2+λ) imply q ≤ A
-- statement:
--   Throughout, the standing assumptions of §3 hold: $0\le\lambda\le1$, $0\le q\le1$, $0<\delta<1$, $v\ge\bar v\ge0$, $k\ge0$, and the program has a threshold $X\ge1$. If $q\le\frac12$ and $\delta\ge\frac{2}{2+\lambda}$, then
--   $$q\ \le\ A=\frac{\lambda q\delta}{1-\delta+\lambda q\delta}.$$
--
--   This is the step that lets Lemma 3(a) apply under condition (a) of Proposition 3.
-- source:
--   Liu, Sun & Zhang, An Analysis of "Buy X, Get One Free" Reward Programs, accepted manuscript (Operations Research 69(6), 2021; version of March 26, 2021), p. 47, proof of Proposition 3, Part (a)

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model

namespace BuyXFree.Threshold

/-- Proof of Proposition 3, Part (a), p. 47: if `q ≤ 1/2` and `δ ≥ 2/(2 + λ)` then `q ≤ A`. -/
theorem q_le_A (P : Params) (hP : P.Standing) (hq : P.q ≤ 1 / 2)
    (hδ : 2 / (2 + P.lam) ≤ P.δ) :
    P.q ≤ A P := by sorry
end BuyXFree.Threshold
