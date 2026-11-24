-- Prove2me | Theorems.Thm_Erdos1219_mk_iUnion_nat_eq_sum
-- name    : Erdos1219.mk_iUnion_nat_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:48.618839+00:00
-- url     : https://prove2.me/theorems/65415207-0694-45f6-80ca-c35b508eb669
-- title:
--   Erdos1219: mk i Union nat eq sum
-- statement:
--   The cardinality of a disjoint `ℕ`-indexed union is the sum of the cardinalities.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L96-L99
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L96-L99

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.mk_iUnion_nat_eq_sum {V : Type u} (t : ℕ → Set V) (h : Pairwise (Disjoint on t)) :
    #(⋃ p, t p) = Cardinal.sum fun p => #(t p) := by sorry
