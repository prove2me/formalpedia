-- Prove2me | Theorems.Thm_CirclePackingConstants_c_n_thirty_six
-- name    : CirclePackingConstants.c_n_thirty_six
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-12T13:29:48.641731+00:00
-- url     : https://prove2.me/theorems/2dcc3df9-abaf-4a08-887c-18813d288745
-- title:
--   Exact packing constant for n = 36
-- statement:
--   Prove the exact grid optimum d₃₆ = 1/5, equivalently c₃₆ = π/4.
-- source:
--   User-supplied Circles in squares: proofs and bounds, pp. 2–3, supplied September 12, 2026.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem c_n_thirty_six :
    c_n 36 = Real.pi / 4 := by sorry
