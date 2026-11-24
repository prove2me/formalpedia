-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_violSet_eq_singleton_of_conflict
-- name    : BSLambda.PartialAssign.violSet_eq_singleton_of_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:35.584728+00:00
-- url     : https://prove2.me/theorems/c2eb23d3-02b7-41ba-b699-ebfa9baf2618
-- title:
--   Partial Assign: viol Set eq singleton of conflict
-- statement:
--   If `x ∈ C(P)`, its `{p, q}`-flip lies in `C(Q)`, `P` and `Q` conflict at `q` and `Q`
--   leaves `p` free, then `q` is the only literal of `Q` that `x` violates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L326-L334
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L326-L334

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.PartialAssign
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem BSLambda.PartialAssign.violSet_eq_singleton_of_conflict {P Q : PartialAssign V} {x : Input V} {p q : V}
    (hx : P.Sat x) (hy : Q.Sat (flipSet x {p, q})) (hc : P.Conflict Q q)
    (hp : p ∉ Q.fixedSet) : Q.violSet x = {q} := by sorry
