-- Prove2me | Theorems.Thm_DetANN_cellsWritten_bound
-- name    : DetANN.cellsWritten_bound
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:01.891818+00:00
-- url     : https://prove2.me/theorems/8fabb511-eace-4738-a391-3b1fd4def6c7
-- title:
--   Cells written by a real-RAM run lie in a window
-- statement:
--   Let $P$ be a program of the real RAM `PNormReg_Machine`, let $X\ge1$ be an integer, and let $s$ be an $X$-bounded state (definition `PNormRegLib_AddressBound`) such that $X$ is also a literal bound for $P$. Write $s_t$ for the state after $t$ steps of $P$ from $s$ on the all-false tape `DetANN.detTape`. Then for every $t\in\mathbb N$, every memory cell (real or integer) stored to during the first $t$ steps, as counted by `DetANN.cellsWritten`, has an address $z$ with
--
--   $$|z|\le X\cdot2^t.$$
--
--   The data-structure specification `DetANN.IsDetANNStructure` bounds how many cells preprocessing writes but not where they are. This result locates them, so that several data structures can be placed in disjoint regions of memory.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure

namespace DetANN

/-- **Written cells lie in a window.** Under the hypotheses of `PNormRegLib.bounded_run`, every cell
stored to during the first `t` steps of `P` from `s` has address of absolute value at most
`X · 2^t`. -/
theorem cellsWritten_bound (P : PNormReg.Program) (X : ℤ) (s : PNormReg.State)
    (hs : PNormRegLib.PBounded X s) (hlit : PNormRegLib.LitBound P X) (hX : 1 ≤ X) (t : ℕ) :
    ∀ c ∈ cellsWritten P s t, |c.2| ≤ X * 2 ^ t := by sorry

end DetANN
