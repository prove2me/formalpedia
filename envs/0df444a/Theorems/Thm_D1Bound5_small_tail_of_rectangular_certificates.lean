-- Prove2me | Theorems.Thm_D1Bound5_small_tail_of_rectangular_certificates
-- name    : D1Bound5.small_tail_of_rectangular_certificates
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:29:24.33867+00:00
-- url     : https://prove2.me/theorems/58d7e924-e09a-457e-aeb3-fe8587627cb4
-- title:
--   Small tail of rectangular certificates
-- statement:
--   A complete checker for the 30-element parameter rectangle suffices for the small-tail regular-completion obstruction. The finite Boolean certificates are separate, still-open obligations.
-- source:
--   D1Bound5/SmallTailRange.lean, lines 23-48, SHA-256 c865f417a7e67904d3233f7fda419d37747223d0ad8cd78c1681f681b53a4c0d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_FiniteTail_Definitions
import Definitions.Def_D1Bound5_Regular_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.small_tail_of_rectangular_certificates
    (certificate : ∀ tau nu : ℤ,
      (tau = 0 ∨ tau = 1) →
      1 ≤ nu → nu ≤ 15 →
      0 < QuadInt.discriminant tau nu →
      SmallTailCheck tau nu)
    {tau nu : ℤ} (htau : tau = 0 ∨ tau = 1)
    (hpos : 0 < QuadInt.discriminant tau nu)
    (a b c d : QuadInt tau nu)
    (ha0 : a ≠ 0) (hd0 : d ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (hNa : a.norm ≤ b.norm) (hNb : 9 ≤ b.norm)
    (hNbc : b.norm ≤ c.norm) (hNc : c.norm ≤ 15) (hNcd : c.norm ≤ d.norm)
    (hsbc : ∃ r, r*r = b*c+1) (hsab : ∃ r, r*r = a*b+1)
    (hsac : ∃ r, r*r = a*c+1) (hsad : ∃ r, r*r = a*d+1)
    (hreg : regularDefect b c d = 0) : False := by sorry

end D1Bound5
end
