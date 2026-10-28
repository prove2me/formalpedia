-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_eval
-- name    : D1Bound5.bennettClearedTaylor_eval
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:39.205533+00:00
-- url     : https://prove2.me/theorems/ff114b52-6c1c-4d2b-a7f2-75543ba3f7ae
-- title:
--   Bennett Cleared Taylor eval
-- statement:
--   Evaluation away from the local origin is a single exact coefficient of the rescaled binomial series times the remaining reciprocal poles.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 32-50, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennettClearedTaylor_eval (k r : ℕ) (hr : r ≤ k) (ν a N : F)
    (B : PowerSeries F) (hd : N + a ≠ 0) :
    (bennettClearedTaylor k r ν a B).eval N =
      (N + a) ^ k * PowerSeries.coeff r
        (PowerSeries.rescale (N + a)⁻¹
          (PowerSeries.binomialSeries F ((k : F) + ν)) * B) := by sorry



section Nodes

variable {I : Type*} [DecidableEq I]

















end Nodes

end D1Bound5
end
