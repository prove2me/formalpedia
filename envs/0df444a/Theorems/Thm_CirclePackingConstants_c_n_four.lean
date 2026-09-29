-- Prove2me | Theorems.Thm_CirclePackingConstants_c_n_four
-- name    : CirclePackingConstants.c_n_four
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-12T13:22:21.288375+00:00
-- url     : https://prove2.me/theorems/6b99f4bd-988a-433e-aa59-a48a7133d2f1
-- title:
--   Exact packing constant for n = 4
-- statement:
--   Prove the exact optimum d₄ = 1, equivalently c₄ = π/4.
-- source:
--   User-supplied Circles in squares: proofs and bounds, pp. 2–3, supplied September 12, 2026.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem c_n_four :
    c_n 4 = Real.pi / 4 := by sorry
