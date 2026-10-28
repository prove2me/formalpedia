-- Prove2me | Theorems.Thm_D1Bound5_bennettClearedResidue_remove_node
-- name    : D1Bound5.bennettClearedResidue_remove_node
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:27.171988+00:00
-- url     : https://prove2.me/theorems/35c5dfa9-d8a6-4903-a18d-fef26e6a3f61
-- title:
--   Bennett Cleared Residue remove node
-- statement:
--   Exact arbitrary-order node removal, including the parameter shift ν-k and the full column scaling. No determinant formula is assumed.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 116-131, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.bennettClearedResidue_remove_node (s : Finset I) (a : I → F)
    (k : ℕ) (ν : F) (i j q : I) (hq : q ∈ s)
    (hiq : i ≠ q) (hjq : j ≠ q) (ha : a j ≠ a q) :
    (bennettClearedResidue s a k ν i j).eval (-a q) =
      ((a j - a q)⁻¹) ^ k *
        (bennettClearedResidue (s.erase q) a k (ν - (k : F)) i j).eval (-a q) := by sorry







end Nodes

end D1Bound5
end
