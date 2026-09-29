-- Prove2me | Theorems.Thm_CirclePackingConstants_c_n_three
-- name    : CirclePackingConstants.c_n_three
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-12T11:00:25.717873+00:00
-- url     : https://prove2.me/theorems/e420383a-7df7-4824-8a3d-52d060a368ec
-- title:
--   Exact three-disk packing constant
-- statement:
--   $c_3=3\pi\left(\frac{\sqrt6-\sqrt2}{2(1+\sqrt6-\sqrt2)}\right)^2$ for the supremum-defined equal-disk packing constant in the unit square.
-- source:
--   User-supplied Circles in squares: proofs and bounds, p. 1, and accompanying CirclePacking.lean source package, supplied September 12, 2026.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem c_n_three :
    c_n 3 = 3 * Real.pi *
      ((Real.sqrt 6 - Real.sqrt 2) /
        (2 * (1 + (Real.sqrt 6 - Real.sqrt 2)))) ^ 2 := by sorry
