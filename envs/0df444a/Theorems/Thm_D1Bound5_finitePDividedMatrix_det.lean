-- Prove2me | Theorems.Thm_D1Bound5_finitePDividedMatrix_det
-- name    : D1Bound5.finitePDividedMatrix_det
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:39:52.529987+00:00
-- url     : https://prove2.me/theorems/af997167-ee53-4a42-9d94-4e71092b05b7
-- title:
--   Finite PDivided Matrix det
-- statement:
--   Exact determinant from the displayed integer polynomials. No rank or leading-coefficient certificate is assumed.
-- source:
--   D1Bound5/FinitePMatrix.lean, lines 72-90, SHA-256 b8a285016f4dd188b4ef52b0d947c0efaeb78e66205e2d778d4892467773abcd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions

section
namespace D1Bound5

variable {R : Type*} [CommRing R]




























set_option maxHeartbeats 4000000 in

theorem _root_.D1Bound5.finitePDividedMatrix_det (a b s c : R) :
    (finitePDividedMatrix a b s c).det =
      -78750*a*b*s*(a-b)^5*(a-s)*(b-s)*finitePDetFactor a b s c := by sorry



end D1Bound5
end
