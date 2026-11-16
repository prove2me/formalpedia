-- Prove2me | Theorems.Thm_DetANN_pbounded_queryState
-- name    : DetANN.pbounded_queryState
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:03.369413+00:00
-- url     : https://prove2.me/theorems/18aee837-017e-4dc0-a239-960dc66c8504
-- title:
--   The query layout preserves boundedness
-- statement:
--   Let $X\ge0$ be an integer, let $s$ be an $X$-bounded state of the real RAM (definition `PNormRegLib_AddressBound`), and let $q\in\mathbb R^m$. Then the query start state of `DetANN.queryState` on $s$ for $q$ is
--
--   $$X\text{-bounded}.$$
--
--   The query layout resets all pointers to $0$ and keeps the integer memory, so the bound reached at the end of preprocessing carries over to the start of every query.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure

namespace DetANN

/-- The query layout on a `PBounded X` state (with `X ≥ 0`) is `PBounded X`: pointers are reset to
`0` and the integer memory is kept. -/
theorem pbounded_queryState (X : ℤ) (s : PNormReg.State) (hs : PNormRegLib.PBounded X s)
    (hX : 0 ≤ X) (m : ℕ) (q : EuclideanSpace ℝ (Fin m)) :
    PNormRegLib.PBounded X (queryState m s q) := by sorry

end DetANN
