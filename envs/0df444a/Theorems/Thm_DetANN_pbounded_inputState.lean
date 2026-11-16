-- Prove2me | Theorems.Thm_DetANN_pbounded_inputState
-- name    : DetANN.pbounded_inputState
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T08:11:07.14071+00:00
-- url     : https://prove2.me/theorems/5ad4fc19-be50-4092-a420-944823651353
-- title:
--   The preprocessing input layout is bounded
-- statement:
--   Let $N,m\in\mathbb N$, let $Y_0,\dots,Y_{N-1}\in\mathbb R^m$ and $\theta\in\mathbb R$. The preprocessing input state of `DetANN.inputState` (integer cells $0,1$ hold $N,m$; real memory holds $\theta$ and the points) is
--
--   $$(N+m+1)\text{-bounded}$$
--
--   in the sense of the definition `PNormRegLib_AddressBound`.
--
--   This is the starting bound needed to apply the address bound `PNormRegLib.bounded_run` to preprocessing.
-- source:
--   Original library result for the PNormReg machine (definition PNormReg_Machine: Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission), written for the mission 'Deterministic Approximate Nearest Neighbors in High Dimensions' at the captain's invitation (mission discussion, 2026-11-14). No external source is claimed; the doubling argument is the standard one for machines whose only integer arithmetic is addition and subtraction.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure

namespace DetANN

/-- The preprocessing input layout of `N` points in `ℝ^m` is `PBounded (N + m + 1)`. -/
theorem pbounded_inputState {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ) :
    PNormRegLib.PBounded ((N : ℤ) + m + 1) (inputState Y θ) := by sorry

end DetANN
