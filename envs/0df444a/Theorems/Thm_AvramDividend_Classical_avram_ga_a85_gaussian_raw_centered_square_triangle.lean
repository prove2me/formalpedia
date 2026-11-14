-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a85_gaussian_raw_centered_square_triangle
-- name    : AvramDividend.Classical.avram_ga_a85_gaussian_raw_centered_square_triangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:01:21.909017+00:00
-- url     : https://prove2.me/theorems/25f0ce98-082d-49c8-b601-3ffa444733bb
-- title:
--   Gaussian physical raw source versus centred source square difference has scalar absolute triangle inequality
-- statement:
--   For real Gaussian centred source increment z and deterministic physical drift d, the absolute squared raw-minus-centred source difference is bounded by twice the absolute drift-centred cross product plus deterministic drift squared.
-- source:
--   Sound direct child for ga_a79 raw-versus-centred original Gaussian quadratic error in b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_ga_a85_gaussian_raw_centered_square_triangle (z d : ℝ) :
    |(z + d)^2 - z^2| ≤ 2 * |d| * |z| + d^2 := by sorry
