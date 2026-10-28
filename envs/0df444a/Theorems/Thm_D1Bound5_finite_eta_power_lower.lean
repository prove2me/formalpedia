-- Prove2me | Theorems.Thm_D1Bound5_finite_eta_power_lower
-- name    : D1Bound5.finite_eta_power_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:15.339461+00:00
-- url     : https://prove2.me/theorems/de3fde00-0182-4910-ae94-2d398a8cc1b0
-- title:
--   Finite eta power lower
-- statement:
--   A single rational comparison controls every exponent appearing in the finite two-anchor families (their largest exponent is17/2).
-- source:
--   D1Bound5/FiniteEtaBound.lean, lines 8-24, SHA-256 bbe0c480ef14e08f89c2bfd31afb3f5e0e4f98178a555879f1db7d5985f98cf6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

section
namespace D1Bound5


theorem _root_.D1Bound5.finite_eta_power_lower (T e : ℝ) (hT : 1000 ≤ T) (he : e ≤ 9) :
    (100/101 : ℝ) < (1-1/T)^e := by sorry



end D1Bound5
end
