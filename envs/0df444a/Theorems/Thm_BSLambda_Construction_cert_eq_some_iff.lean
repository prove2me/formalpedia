-- Prove2me | Theorems.Thm_BSLambda_Construction_cert_eq_some_iff
-- name    : BSLambda.Construction.cert_eq_some_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:32.796809+00:00
-- url     : https://prove2.me/theorems/90d91913-b651-4be8-be2b-92358f94eaf2
-- title:
--   Construction: cert eq some iff
-- statement:
--   The literals of `P_i`: it fixes `v` to `true` on the owner block `B_i`, and to `false`
--   on the gate coordinate of an outgoing arc.  Every other lemma of this section is a
--   specialisation of this one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L104-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L104-L108

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

theorem BSLambda.Construction.cert_eq_some_iff :
    cert Arc γ i v = some b ↔
      (v.1 = i ∧ b = true) ∨ (v.1 ≠ i ∧ Arc i v.1 ∧ v.2 = γ i v.1 ∧ b = false) := by sorry
