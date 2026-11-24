-- Prove2me | Theorems.Thm_Erdos1219_nonempty_of_mk_eq
-- name    : Erdos1219.nonempty_of_mk_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:20.493948+00:00
-- url     : https://prove2.me/theorems/8dfb8be5-d596-45d6-857c-232c82c59980
-- title:
--   Erdos1219: nonempty of mk eq
-- statement:
--   The Erdos1219 construction uses the nonempty of mk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L116-L119
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L116-L119

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.nonempty_of_mk_eq {V : Type u} {s : Set V} {c : Cardinal.{u}} (hs : #s = c)
    (hc : ℵ₀ ≤ c) : s.Nonempty := by sorry
