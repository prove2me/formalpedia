-- Prove2me | Theorems.Thm_Erdos1219_mk_iUnion_lt_of_isRegular
-- name    : Erdos1219.mk_iUnion_lt_of_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:12.904285+00:00
-- url     : https://prove2.me/theorems/c1be03d8-4e20-4e65-8d7b-933f10fe7b65
-- title:
--   Erdos1219: mk i Union lt of is Regular
-- statement:
--   A union of fewer than `c` sets, each of cardinality `< c`, has cardinality `< c` when `c`
--   is regular.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L17-L19
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L17-L19

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.mk_iUnion_lt_of_isRegular {V ι : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (hι : #ι < c) (t : ι → Set V) (ht : ∀ i, #(t i) < c) : #(⋃ i, t i) < c := by sorry
