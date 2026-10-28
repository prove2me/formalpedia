-- Prove2me | Theorems.Thm_D1Bound5_unit_pair_cubic_numeric
-- name    : D1Bound5.unit_pair_cubic_numeric
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:29:11.414157+00:00
-- url     : https://prove2.me/theorems/0f7a755c-38a7-4669-9521-a58ef82ebd32
-- title:
--   Unit pair cubic numeric
-- statement:
--   Second-order cancellation converts two first-order root estimates into the cubic unit-pair gap. The lower bound on L is supplied by integrality, not assumed in the eventual tuple theorem.
-- source:
--   D1Bound5/UnitPairCubicNumeric.lean, lines 16-64, SHA-256 8c7ff651911ee31cb8b29e22e5594dd428c04a7b2295263089a9dfbaf6358898. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.unit_pair_cubic_numeric (C D Z W E F L : ℝ)
    (hC : 9 ≤ C) (hCD : C ≤ D) (hZ0 : 0 < Z) (hW0 : 0 < W)
    (hE0 : 0 ≤ E) (hF0 : 0 ≤ F) (hL : 1 ≤ L)
    (hW : W ≤ C+D) (hZ : C*D ≤ Z^2+1)
    (hE : (15/8 : ℝ)*Z*E < W) (hF : (15/8 : ℝ)*Z*F < W)
    (hcancel : 2*Z*L ≤ E^2+F^2) : C^3/2 < D := by sorry

end D1Bound5
end
