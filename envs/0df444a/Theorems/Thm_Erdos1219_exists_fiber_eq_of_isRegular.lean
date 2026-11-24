-- Prove2me | Theorems.Thm_Erdos1219_exists_fiber_eq_of_isRegular
-- name    : Erdos1219.exists_fiber_eq_of_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:20.016894+00:00
-- url     : https://prove2.me/theorems/69442870-14c0-49f3-9b5e-dbcc1793cbd1
-- title:
--   Erdos1219: exists fiber eq of is Regular
-- statement:
--   Pigeonhole for regular cardinals: a set of regular cardinality `c` mapped into a type of
--   cardinality `< c` has a fibre of cardinality `c`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L23-L32
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L23-L32

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.exists_fiber_eq_of_isRegular {V T : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (s : Set V) (hs : #s = c) (φ : V → T) (hT : #T < c) :
    ∃ t, #(s ∩ φ ⁻¹' {t} : Set V) = c := by sorry
