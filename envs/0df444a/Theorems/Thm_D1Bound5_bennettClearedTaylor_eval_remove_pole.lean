-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedTaylor_eval_remove_pole
-- name    : D1Bound5.bennettClearedTaylor_eval_remove_pole
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:46.312444+00:00
-- url     : https://prove2.me/theorems/1616ea30-05ba-475d-a8e2-f58032282df2
-- title:
--   Bennett Cleared Taylor eval remove pole
-- statement:
--   The single-pole node-removal identity is precisely Chu--Vandermonde, expressed by multiplication of formal binomial series.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 52-80, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettClearedResidues_Definitions
import Definitions.Def_D1Bound5_BennettPoleSeries_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]








theorem _root_.D1Bound5.bennettClearedTaylor_eval_remove_pole
    (k r : ℕ) (hr : r ≤ k) (ν a N : F) (B : PowerSeries F)
    (hd : N + a ≠ 0) :
    (bennettClearedTaylor k r ν a
      (bennettPoleSeries (N + a) k * B)).eval N =
      ((N + a)⁻¹) ^ k *
        (bennettClearedTaylor k r (ν - (k : F)) a B).eval N := by sorry

section Nodes

variable {I : Type*} [DecidableEq I]

















end Nodes

end D1Bound5
end
