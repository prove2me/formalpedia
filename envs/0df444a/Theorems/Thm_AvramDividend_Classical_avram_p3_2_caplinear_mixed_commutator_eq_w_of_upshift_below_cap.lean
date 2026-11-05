-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap
-- name    : AvramDividend.Classical.avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:07:24.995353+00:00
-- url     : https://prove2.me/theorems/3d52f814-6565-4de6-8858-ca9aa36c7a9e
-- title:
--   Original cap-linear mixed drift/raw-J commutator equals true w on the closed cap including cap contact
-- statement:
--   For the cap-linear extension V of candidate w and negative raw-jump mass j>=0, if physical reserve z and drift-upshift z+c are within closed cap (or C infinite), all four mixed-commutator V evaluations equal w even at cap contact and negative values.
-- source:
--   Exact cap-linear four-point identity for original source mesh and F2 compact-interior localisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_caplinear_mixed_commutator_eq_w_of_upshift_below_cap
    (w : ℝ → ℝ) (C : ℝ≥0∞) (z c j : ℝ)
    (hz : C = ⊤ ∨ z ≤ C.toReal)
    (hup : C = ⊤ ∨ z + c ≤ C.toReal)
    (hj : 0 ≤ j) :
    let V : ℝ → ℝ := fun r =>
      if C = ⊤ then w r else if r ≤ C.toReal then w r
      else w C.toReal + (r - C.toReal)
    V (z + c - j) - V (z + c) - V (z - j) + V z =
      w (z + c - j) - w (z + c) - w (z - j) + w z := by sorry
