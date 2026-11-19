-- Prove2me | Theorems.Thm_ArithmeticKakeya_katz_tao_config_7_4
-- name    : ArithmeticKakeya.katz_tao_config_7_4
-- status  : Open
-- author  : @LG
-- created : 2026-11-16T21:57:23.315201+00:00
-- url     : https://prove2.me/theorems/8c64aef7-1b8a-4b41-9e99-16ca0248e850
-- title:
--   Katz–Tao configuration of score $7/4$
-- statement:
--   The second Katz–Tao configuration: for $X=\{(1,0),(0,1),(1,2),(1,1)\}$ there is a forcing constructible proof of score $\le 7/4$. Their explicit example has $n=4$, $m=4$, $|R|=3$, $|T|=0$, giving $(4+3)/(4-0)=7/4$; adding the dilate $(1,2)$ improves on $11/6$.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (The second Katz-Tao configuration)

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing

namespace ArithmeticKakeya
theorem katz_tao_config_7_4 :
    ∃ (G : ConstructibleGraph ({(1, 0), (0, 1), (1, 2), (1, 1)} : Finset (ℤ × ℤ)))
      (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)),
      IsXSet G R T ∧ Forces G R T ∧ T.length < n G ∧
      4 * (m G + R.length) ≤ 7 * (n G - T.length) := by sorry
end ArithmeticKakeya
