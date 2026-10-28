-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedResidue_diagonal_at_node
-- name    : D1Bound5.bennettClearedResidue_diagonal_at_node
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:36:06.278998+00:00
-- url     : https://prove2.me/theorems/a221d597-ecda-4ca6-9ba5-5311f44f9ae6
-- title:
--   Bennett Cleared Residue diagonal at node
-- statement:
--   The surviving diagonal entry at the removed node, with its exact generalized binomial coefficient and every directed node difference.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 153-185, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

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
















theorem _root_.D1Bound5.bennettClearedResidue_diagonal_at_node
    (s : Finset I) (a : I → F) (k : ℕ) (ν : F) (i : I) :
    (bennettClearedResidue s a k ν i i).eval (-a i) =
      Ring.choose ((k : F) + ν) k *
        ∏ l ∈ s.erase i, ((a i - a l)⁻¹) ^ k := by sorry

end Nodes

end D1Bound5
end
