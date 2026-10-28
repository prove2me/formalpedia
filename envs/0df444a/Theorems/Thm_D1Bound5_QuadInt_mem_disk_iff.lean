-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_mem_disk_iff
-- name    : D1Bound5.QuadInt.mem_disk_iff
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:55:20.724303+00:00
-- url     : https://prove2.me/theorems/cd34cb13-7ff1-4b3a-95c2-f85854fdb456
-- title:
--   Quad Int — mem disk iff
-- statement:
--   Exact completeness and soundness of disk enumeration. This is valid for every integer cutoff, including an empty negative-cutoff disk.
-- source:
--   D1Bound5/DiskEnumeration.lean, lines 30-73, SHA-256 d1d1de7efa3c474d4e36936ae73c743f9c42044bc9487e406a2818230fd2ca53. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions

section
namespace D1Bound5.QuadInt

variable {tau nu : ℤ}






theorem _root_.D1Bound5.QuadInt.mem_disk_iff (hd : 0 < discriminant tau nu) (M : ℤ) (z : QuadInt tau nu) :
    z ∈ disk tau nu M ↔ z.norm ≤ M := by sorry





end D1Bound5.QuadInt
end
