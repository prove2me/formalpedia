-- Prove2me | Theorems.Thm_D1Bound5_coherent_cpow_half_sub_one_norm_le
-- name    : D1Bound5.coherent_cpow_half_sub_one_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:30:52.39601+00:00
-- url     : https://prove2.me/theorems/ce4e792a-e119-490d-b8bf-7d625d18e13d
-- title:
--   Coherent cpow half sub one norm le
-- statement:
--   A geometric bound for the actual principal half-power remainder. This follows from its convergent binomial series and the coefficient bound `|b_n| <= 1/2`, without selecting a new square-root sign.
-- source:
--   D1Bound5/CoherentNearOne.lean, lines 7-46, SHA-256 2bc9cb36fbc13ebd4a45c12aad522c318dab7df9ff1f0b30190b7ecf486f48dd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_cpow_half_sub_one_norm_le
    (w : ℂ) (hw : ‖w‖ < 1) :
    ‖((1 + w) ^ (1 / 2 : ℂ)) - 1‖ ≤
      (1 / 2 : ℝ) * ‖w‖ / (1 - ‖w‖) := by sorry



end D1Bound5
end
