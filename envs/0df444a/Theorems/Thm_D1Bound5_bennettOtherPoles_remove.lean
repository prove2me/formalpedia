-- Prove2me | Theorems.Thm_D1Bound5_bennettOtherPoles_remove
-- name    : D1Bound5.bennettOtherPoles_remove
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:35:32.585226+00:00
-- url     : https://prove2.me/theorems/14977d4f-c08b-4d10-9176-0d4b953ed627
-- title:
--   Bennett Other Poles remove
-- statement:
--   Removing a different node splits off exactly its reciprocal pole.
-- source:
--   D1Bound5/BennettClearedResidues.lean, lines 104-114, SHA-256 ec76df5d4e2c4d6b07d0919f3d7f1eca9b85a57c220d930e6ae87c93827d8f29. Project: https://github.com/tomislav-math/d1-bound5-lean

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









section Nodes

variable {I : Type*} [DecidableEq I]








theorem _root_.D1Bound5.bennettOtherPoles_remove (s : Finset I) (a : I → F)
    (k : ℕ) (i j q : I) (hq : q ∈ s) (hiq : i ≠ q) (hjq : j ≠ q) :
    bennettOtherPoles s a k i j =
      bennettPoleSeries (a j - a q) k *
        bennettOtherPoles (s.erase q) a k i j := by sorry









end Nodes

end D1Bound5
end
