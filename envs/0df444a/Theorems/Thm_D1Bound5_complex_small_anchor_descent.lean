-- Prove2me | Theorems.Thm_D1Bound5_complex_small_anchor_descent
-- name    : D1Bound5.complex_small_anchor_descent
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:41.488582+00:00
-- url     : https://prove2.me/theorems/451bca59-803a-444f-b866-8f1906f6e742
-- title:
--   Complex small anchor descent
-- statement:
--   The analytic part of the small-anchor descent. The sole arithmetic input is the multiplier norm bound, supplied separately from integrality. The square root sign is chosen by the already proved perturbation lemma.
-- source:
--   D1Bound5/DescentNorm.lean, lines 48-132, SHA-256 e450f6421d89ae185f5175e96fab77ed2aaba23eeb69a15bfdb754a53e2854b4. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.complex_small_anchor_descent
    (a b z r0 r s : ℂ)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1)
    (hA : ‖a‖ < 3) (hB : ‖b‖ < 3)
    (hp : 1 ≤ ‖a*b‖) (hZ : 33 ≤ ‖z‖)
    (hhyper : 7 ≤ ‖2*a*b+1‖^2) :
    ‖mutate a b z r0 r s‖ < ‖z‖/5+26 ∨
      ‖mutate a b z r0 r (-s)‖ < ‖z‖/5+26 := by sorry

end D1Bound5
end
