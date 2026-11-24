-- Prove2me | Theorems.Thm_Erdos1219_sum_eq_of_interlaced
-- name    : Erdos1219.sum_eq_of_interlaced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:37.910943+00:00
-- url     : https://prove2.me/theorems/cf04920b-933f-432e-81aa-f6c94bfab43a
-- title:
--   Erdos1219: sum eq of interlaced
-- statement:
--   Two interlaced `ℕ`-indexed families have the same sum.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L79-L81
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L79-L81

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.sum_eq_of_interlaced (a b : ℕ → Cardinal.{u}) (h1 : ∀ k, a k ≤ b k)
    (h2 : ∀ k, b k ≤ a (k + 1)) : Cardinal.sum a = Cardinal.sum b := by sorry
