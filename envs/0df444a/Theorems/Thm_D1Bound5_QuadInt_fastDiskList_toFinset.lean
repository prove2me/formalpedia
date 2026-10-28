-- Prove2me | Theorems.Thm_D1Bound5_QuadInt_fastDiskList_toFinset
-- name    : D1Bound5.QuadInt.fastDiskList_toFinset
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:53.202366+00:00
-- url     : https://prove2.me/theorems/3c54b48b-5c76-4448-82da-2f9a63cc44dd
-- title:
--   Quad Int — fast Disk List to Finset
-- statement:
--   A propositional bridge to the existing complete disk enumeration. The proof does not evaluate a finite set of concrete coordinates.
-- source:
--   D1Bound5/FastDiskList.lean, lines 30-41, SHA-256 60afd777700a3d6a319be0b0145eb86a6f1657a58e26c7947467097b7c482fed. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_FastDiskList_Definitions

section
namespace D1Bound5
namespace QuadInt








theorem _root_.D1Bound5.QuadInt.fastDiskList_toFinset (tau nu M : ℤ) :
    (fastDiskList tau nu M).toFinset = disk tau nu M := by sorry

end QuadInt
end D1Bound5
end
