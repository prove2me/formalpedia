-- Prove2me | Theorems.Thm_DedekindSubgroups_sig_injOn
-- name    : DedekindSubgroups.sig_injOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:05:20.722606+00:00
-- url     : https://prove2.me/theorems/fe6df7ad-4635-5a0b-9367-e323c92e66ca
-- title:
--   Dedekind Subgroups: sig inj On
-- statement:
--   The Dedekind Subgroups construction uses the sig inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L25-L27
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Parity.lean#L25-L27

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity
set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sig_injOn (hinv : h * h' % k = 1) {x y : ℕ} (hx : x < k) (hy : y < k)
    (he : sig h k x = sig h k y) : x = y := by sorry
