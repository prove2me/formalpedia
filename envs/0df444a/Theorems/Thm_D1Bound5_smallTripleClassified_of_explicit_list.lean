-- Prove2me | Theorems.Thm_D1Bound5_smallTripleClassified_of_explicit_list
-- name    : D1Bound5.smallTripleClassified_of_explicit_list
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:19.772988+00:00
-- url     : https://prove2.me/theorems/25dcaa3f-c24b-44cd-a99e-7a1bb556ee40
-- title:
--   Small Triple Classified of explicit list
-- statement:
--   Soundness of the complete small-triple classifier.
-- source:
--   D1Bound5/SmallTripleCheck.lean, lines 29-58, SHA-256 1f75bcdaa9e326145897ef273ea3989447fff478e71849b1db21c3aa9abd5c19. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_DiskEnumeration_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions

section
namespace D1Bound5
open QuadInt






theorem _root_.D1Bound5.smallTripleClassified_of_explicit_list {tau nu : ℤ}
    (hpos : 0 < discriminant tau nu)
    (xs : List (QuadInt tau nu)) (rows : List (Finset (ℤ × ℤ)))
    (cover : ∀ z ∈ disk tau nu 8, z ∈ xs)
    (checked : smallTripleClassifiedBool xs rows = true)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ rows := by sorry

end D1Bound5
end
