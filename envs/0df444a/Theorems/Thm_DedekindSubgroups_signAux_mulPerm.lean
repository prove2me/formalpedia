-- Prove2me | Theorems.Thm_DedekindSubgroups_signAux_mulPerm
-- name    : DedekindSubgroups.signAux_mulPerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:05:28.454086+00:00
-- url     : https://prove2.me/theorems/63eaf41b-f58b-5ac2-bd34-37317722183d
-- title:
--   Dedekind Subgroups: sign Aux mul Perm
-- statement:
--   The Dedekind Subgroups construction uses the sign Aux mul Perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L80-L108
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L80-L108

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.signAux_mulPerm (hk : 0 < k) (hinv : h * h' % k = 1) :
    Perm.signAux (mulPerm hk hinv) = (-1) ^ inv h k := by sorry
