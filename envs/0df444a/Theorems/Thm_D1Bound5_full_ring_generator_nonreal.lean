-- Prove2me | Theorems.Thm_D1Bound5_full_ring_generator_nonreal
-- name    : D1Bound5.full_ring_generator_nonreal
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:53:46.424752+00:00
-- url     : https://prove2.me/theorems/a920f523-888e-4cb0-8908-72ee98e92bfa
-- title:
--   Full ring generator nonreal
-- statement:
--   A generator of the full number ring cannot have a real image in a complex embedding of a totally complex field. Fraction representations extend reality from the integer ring to the whole field.
-- source:
--   D1Bound5/FullRingBridge.lean, lines 13-35, SHA-256 dc7878b5987408dc5ad74248ad83af5608a906791f27df468ed3d05ac252ac2f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
open scoped NumberField ComplexConjugate
open Module

namespace D1Bound5

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]


theorem _root_.D1Bound5.full_ring_generator_nonreal {tau nu : ℤ}
    (e : QuadInt tau nu ≃+* 𝓞 K) (φ : K →+* ℂ) :
    (((φ.comp (algebraMap (𝓞 K) K)).comp e.toRingHom) QuadraticAlgebra.omega).im ≠ 0 := by sorry









end D1Bound5
end
