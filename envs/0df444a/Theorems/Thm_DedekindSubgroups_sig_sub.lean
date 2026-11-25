-- Prove2me | Theorems.Thm_DedekindSubgroups_sig_sub
-- name    : DedekindSubgroups.sig_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:04:32.437116+00:00
-- url     : https://prove2.me/theorems/3a7f68b8-3f74-473f-8ebe-bed1904f05fa
-- title:
--   Dedekind Subgroups: sig sub
-- statement:
--   The basic pointwise identity: for `x ≤ y`,
--   `σ(y) - σ(x) = σ(y - x) - k [σ(y) < σ(x)]`.
--
--   Source: https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L24-L89
-- source:
--   https://github.com/jkfarland-bot/DedekindSubgroups-lean/blob/cb87faf157821154dc1beef7aad753d889211ad9/DedekindSubgroups/Meyer.lean#L24-L89

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups

theorem DedekindSubgroups.sig_sub (h k x y : ℕ) (hk : 0 < k) (hxy : x ≤ y) :
    (sig h k y : ℤ) - sig h k x
      = sig h k (y - x) - k * (if sig h k y < sig h k x then 1 else 0) := by sorry
