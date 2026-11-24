-- Prove2me | Theorems.Thm_BSLambda_Construction_arc_and_snd_eq_of_cert_eq_some
-- name    : BSLambda.Construction.arc_and_snd_eq_of_cert_eq_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:56.148282+00:00
-- url     : https://prove2.me/theorems/ad32d1d3-28f5-4ff0-8971-8483896a98f1
-- title:
--   Construction: arc and snd eq of cert eq some
-- statement:
--   Outside its owner block, the only coordinates `P_i` fixes are the gate coordinates
--   `(j, γ(i,j))` of its outgoing arcs `i → j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L130-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L130-L133

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}

theorem BSLambda.Construction.arc_and_snd_eq_of_cert_eq_some (h : v.1 ≠ i) (hb : cert Arc γ i v = some b) :
    Arc i v.1 ∧ v.2 = γ i v.1 := by sorry
