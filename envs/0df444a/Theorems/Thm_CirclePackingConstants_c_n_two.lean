-- Prove2me | Theorems.Thm_CirclePackingConstants_c_n_two
-- name    : CirclePackingConstants.c_n_two
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-12T10:57:38.649623+00:00
-- url     : https://prove2.me/theorems/3898f0d5-b57b-4c7c-ac5d-7c9302ca21bd
-- title:
--   Exact two-disk packing constant
-- statement:
--   $c_2=\pi(3-2\sqrt2)$ for the supremum-defined equal-disk packing constant in the unit square.
-- source:
--   User-supplied Circles in squares: proofs and bounds, p. 1, and accompanying CirclePacking.lean source package, supplied September 12, 2026.

import Definitions.Def_CirclePackingConstants

noncomputable section

namespace CirclePackingConstants

theorem c_n_two :
    c_n 2 = Real.pi * (3 - 2 * Real.sqrt 2) := by sorry
