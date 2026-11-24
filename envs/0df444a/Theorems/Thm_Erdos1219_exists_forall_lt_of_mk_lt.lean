-- Prove2me | Theorems.Thm_Erdos1219_exists_forall_lt_of_mk_lt
-- name    : Erdos1219.exists_forall_lt_of_mk_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:22.565466+00:00
-- url     : https://prove2.me/theorems/1b1911b3-7e0f-46f4-b59f-934dbcfd6abf
-- title:
--   Erdos1219: exists forall lt of mk lt
-- statement:
--   In a well-order of regular cardinality `#X` whose order type is the initial ordinal
--   `(#X).ord`, every subset of cardinality `< #X` is strictly bounded.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L29-L37
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/UnbalancedErdosRado.lean#L29-L37

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]

theorem Erdos1219.exists_forall_lt_of_mk_lt (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X)
    {s : Set X} (hs : #s < #X) : ∃ x, ∀ y ∈ s, y < x := by sorry
