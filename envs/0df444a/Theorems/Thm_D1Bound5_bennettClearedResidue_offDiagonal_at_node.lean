-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedResidue_offDiagonal_at_node
-- name    : D1Bound5.bennettClearedResidue_offDiagonal_at_node
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:33:49.153933+00:00
-- url     : https://prove2.me/theorems/4cb0e509-1fb9-44fb-8343-4dff388ac60a
-- title:
--   Bennett Cleared Residue off Diagonal at node
-- statement:
--   At N=-a_j the off-diagonal part of column j vanishes identically.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 133-146, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

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









section Nodes

variable {I : Type*} [DecidableEq I]












theorem _root_.D1Bound5.bennettClearedResidue_offDiagonal_at_node
    (s : Finset I) (a : I → F) (k : ℕ) (hk : 1 ≤ k) (ν : F)
    (i j : I) (hij : i ≠ j) :
    (bennettClearedResidue s a k ν i j).eval (-a j) = 0 := by sorry





end Nodes

end D1Bound5
end
