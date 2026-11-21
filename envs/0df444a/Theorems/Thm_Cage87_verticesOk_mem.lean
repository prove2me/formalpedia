-- Prove2me | Theorems.Thm_Cage87_verticesOk_mem
-- name    : Cage87.verticesOk_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T20:18:28.400201+00:00
-- url     : https://prove2.me/theorems/5966bae7-4d87-4662-9814-b8e32fe9a150
-- title:
--   Cage87: vertices Ok mem
-- statement:
--   A successful chunk check covers each of its vertices.
--
--   Source: https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Check.lean#L78-L88
-- source:
--   https://github.com/arhancanli/quantavane-cage-8-7/blob/593719d9713eaf81f23e2364e973824ac208bbc4/Cage87/Check.lean#L78-L88

module
public import Definitions.Def_Cage87_Check
set_option autoImplicit true
@[expose] public section
public section
open Cage87

theorem Cage87.verticesOk_mem (adj : Trie) : ∀ (lo c : Nat), verticesOk adj lo c = true →
    ∀ v, lo ≤ v → v < lo + c → vertexOk adj v = true := by sorry
