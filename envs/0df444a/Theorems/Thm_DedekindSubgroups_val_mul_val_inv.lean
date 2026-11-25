-- Prove2me | Theorems.Thm_DedekindSubgroups_val_mul_val_inv
-- name    : DedekindSubgroups.val_mul_val_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:06:54.038712+00:00
-- url     : https://prove2.me/theorems/5a743518-194e-400b-9474-871239554403
-- title:
--   Dedekind Subgroups: val mul val inv
-- statement:
--   The Dedekind Subgroups construction uses the val mul val inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Main.lean#L22-L25
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Main.lean#L22-L25

module
public import Definitions.Def_DedekindSubgroups_Parity
public import Definitions.Def_DedekindSubgroups_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
omit [NeZero k]

theorem DedekindSubgroups.val_mul_val_inv (hk : 1 < k) (u : (ZMod k)ˣ) :
    (u : ZMod k).val * ((u⁻¹ : (ZMod k)ˣ) : ZMod k).val % k = 1 := by sorry
