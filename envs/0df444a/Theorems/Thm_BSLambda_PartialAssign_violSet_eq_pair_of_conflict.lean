-- Prove2me | Theorems.Thm_BSLambda_PartialAssign_violSet_eq_pair_of_conflict
-- name    : BSLambda.PartialAssign.violSet_eq_pair_of_conflict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:51:41.346708+00:00
-- url     : https://prove2.me/theorems/4271fed9-33e8-4c69-99b0-cc959f3acf7c
-- title:
--   Partial Assign: viol Set eq pair of conflict
-- statement:
--   In the situation of `violSet_eq_singleton_of_conflict`, if instead `P` does fix `p`,
--   then the flipped point violates exactly the two literals `p` and `q` of `P`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L338-L347
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Subcube.lean#L338-L347

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

theorem BSLambda.PartialAssign.violSet_eq_pair_of_conflict {P Q : PartialAssign V} {x : Input V} {p q : V}
    (hx : P.Sat x) (hy : Q.Sat (flipSet x {p, q})) (hc : P.Conflict Q q)
    (hp : p ∈ P.fixedSet) : P.violSet (flipSet x {p, q}) = {p, q} := by sorry
