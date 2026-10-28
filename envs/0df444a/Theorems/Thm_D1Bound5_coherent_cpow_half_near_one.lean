-- Prove2me | Theorems.Thm_D1Bound5_coherent_cpow_half_near_one
-- name    : D1Bound5.coherent_cpow_half_near_one
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:11:17.575109+00:00
-- url     : https://prove2.me/theorems/bd74b7d2-9424-418c-84b2-64a2944865fa
-- title:
--   Coherent cpow half near one
-- statement:
--   The four near-one estimates in the manuscript, for the actual analytic branch. Rationalization uses its exact square and the small binomial remainder, rather than any assumed sign of a square root.
-- source:
--   D1Bound5/CoherentNearOne.lean, lines 48-114, SHA-256 2bc9cb36fbc13ebd4a45c12aad522c318dab7df9ff1f0b30190b7ecf486f48dd. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.coherent_cpow_half_near_one
    (w : ℂ) (hw0 : w ≠ 0) (hw : ‖w‖ < (1 / 10000 : ℝ)) :
    (99 / 100 : ℝ) < ‖(1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖(1 + w) ^ (1 / 2 : ℂ)‖ < (101 / 100 : ℝ) ∧
    (100 / 201 : ℝ) * ‖w‖ < ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ ∧
    ‖1 - (1 + w) ^ (1 / 2 : ℂ)‖ < (100 / 199 : ℝ) * ‖w‖ := by sorry

end D1Bound5
end
