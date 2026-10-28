-- Prove2me | Theorems.Thm_D1Bound5_mixed_offDiagonal_cofactor_radius
-- name    : D1Bound5.mixed_offDiagonal_cofactor_radius
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:32.012486+00:00
-- url     : https://prove2.me/theorems/8f559fbb-b89c-4ef9-9a63-3c3a3793b6da
-- title:
--   Mixed off Diagonal cofactor radius
-- statement:
--   Cubic cofactor perturbation bound with six independent error radii.
-- source:
--   D1Bound5/MixedAdjugateScalarBound.lean, lines 87-187, SHA-256 49eb841683fd0e7279ce3834daa64c9419ba6b50d0b8860f85374b8a0264de2d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

section
open scoped Matrix.Norms.L2Operator
open Matrix

namespace D1Bound5







end D1Bound5


namespace D1Bound5


theorem _root_.D1Bound5.mixed_offDiagonal_cofactor_radius (x y z u v w : ℂ)
    (rx ry rz ru rv rw : ℝ)
    (hrx : 0 ≤ rx) (hry : 0 ≤ ry) (hrz : 0 ≤ rz)
    (hru : 0 ≤ ru) (hrv : 0 ≤ rv) (hrw : 0 ≤ rw)
    (hx : ‖x-(1/2 : ℂ)‖ ≤ rx)
    (hy : ‖y-(1/2 : ℂ)‖ ≤ ry)
    (hz : ‖z-(1/2 : ℂ)‖ ≤ rz)
    (hu : ‖u-(1/2 : ℂ)‖ ≤ ru)
    (hv : ‖v-(1/2 : ℂ)‖ ≤ rv)
    (hw : ‖w-(1/2 : ℂ)‖ ≤ rw) :
    ‖w^2*x-w*z*u-w*y*v+(1/8 : ℂ)‖ ≤
      (rx+rz+ru+ry+rv)/4 +
      rw*(rx+(rz+ru+ry+rv)/2) +
      (rw^2+rz*ru+ry*rv)/2 +
      rw*(rx*rw+rz*ru+ry*rv) := by sorry





end D1Bound5
end
