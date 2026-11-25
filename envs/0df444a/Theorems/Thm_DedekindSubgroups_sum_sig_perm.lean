-- Prove2me | Theorems.Thm_DedekindSubgroups_sum_sig_perm
-- name    : DedekindSubgroups.sum_sig_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:03:57.452971+00:00
-- url     : https://prove2.me/theorems/e9ad0bd0-974f-5922-918e-c8de2d878b12
-- title:
--   Dedekind Subgroups: sum sig perm
-- statement:
--   Multiplication by an invertible `h` permutes `{0, …, k-1}`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L138-L153
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L138-L153

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}

theorem DedekindSubgroups.sum_sig_perm {M : Type*} [AddCommMonoid M] (hk : 0 < k) (hinv : h * h' % k = 1)
    (f : ℕ → M) : ∑ r ∈ range k, f (sig h k r) = ∑ r ∈ range k, f r := by sorry
