-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_complex_generator_parameters
-- name    : D1Bound5.QuadInt.complex_generator_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:52:42.505954+00:00
-- url     : https://prove2.me/theorems/b7637e20-885f-429e-bd71-71ae4e9b6c9c
-- title:
--   Quad Int — complex generator parameters
-- statement:
--   A nonreal quadratic generator has real part tau/2 and norm nu.
-- source:
--   D1Bound5/ComplexCoordinates.lean, lines 20-48, SHA-256 1683447b1e232bc1f4d7a3f22a33ac3030c9c47df02e5a5ff8d90857c32c1858. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions

section
namespace D1Bound5.QuadInt

open scoped QuadraticAlgebra

variable {tau nu : ℤ}




theorem _root_.D1Bound5.QuadInt.complex_generator_parameters (f : QuadInt tau nu →+* ℂ)
    (hi : (f QuadraticAlgebra.omega).im ≠ 0) :
    2*(f QuadraticAlgebra.omega).re = (tau : ℝ) ∧
    (f QuadraticAlgebra.omega).re^2 + (f QuadraticAlgebra.omega).im^2 = (nu : ℝ) ∧
    (discriminant tau nu : ℝ) = 4*(f QuadraticAlgebra.omega).im^2 := by sorry







end D1Bound5.QuadInt
end
