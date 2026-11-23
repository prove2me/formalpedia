-- Prove2me | Theorems.Thm_DetANN_RelocCall_pbounded_queryState_of_run
-- name    : DetANN.RelocCall.pbounded_queryState_of_run
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:47.311351+00:00
-- url     : https://prove2.me/theorems/56fd8f96-e1f2-4826-aee8-570c0f43e8cb
-- title:
--   Address bound for a query after opaque preprocessing
-- statement:
--   Let $\operatorname{Pre}$ be any real-RAM preprocessing program whose integer literals are bounded by $X\ge1$, and suppose $N+m+1\le X$. After $t$ deterministic steps from the standard input state for $Y:[N]\to\mathbb R^m$ and $\theta$, every query start state on the resulting memory satisfies
--
--   $$
--   \operatorname{PBounded}\!\left(X2^t,
--     \operatorname{queryState}\!\left(m,
--       \operatorname{run}(\operatorname{Pre},\operatorname{inputState}(Y,\theta),t),q\right)\right).
--   $$
--
--   This propagates the input bound through preprocessing by `bounded_run`, then uses the fact that constructing a query state resets pointers and preserves integer memory. The formula also applies at a preprocessing halt, but no haltedness hypothesis is necessary. It supplies the initial `PBounded` certificate needed to relocate an opaque query program, with window radius chosen using the subsequent query time.
-- source:
--   Original address-bound adapter for the relocated local data structures in Feng--Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission, §7.4, p.19; combines PNormRegLib.bounded_run, DetANN.pbounded_inputState and DetANN.pbounded_queryState.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_PNormRegLib_bounded_run
import Theorems.Thm_DetANN_pbounded_inputState
import Theorems.Thm_DetANN_pbounded_queryState

open PNormReg PNormRegLib DetANN in
/-- If `X` bounds both the literals of `Pre` and its input state, then after `t` preprocessing steps,
the standard start state of every query on the resulting memory is `X * 2^t`-bounded. -/
theorem DetANN.RelocCall.pbounded_queryState_of_run {N m : ℕ}
    (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ)
    (Pre : Program) (X : ℤ) (hlit : LitBound Pre X) (hX : 1 ≤ X)
    (hNX : (N : ℤ) + m + 1 ≤ X) (t : ℕ) (q : EuclideanSpace ℝ (Fin m)) :
    PBounded (X * 2 ^ t) (queryState m (run Pre (inputState Y θ) detTape t) q) := by sorry
