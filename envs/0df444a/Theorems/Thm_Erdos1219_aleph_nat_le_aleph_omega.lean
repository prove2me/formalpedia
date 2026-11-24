-- Prove2me | Theorems.Thm_Erdos1219_aleph_nat_le_aleph_omega
-- name    : Erdos1219.aleph_nat_le_aleph_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:41.422803+00:00
-- url     : https://prove2.me/theorems/b8e9d0bf-a74e-456a-a701-723f8dbda9c3
-- title:
--   Erdos1219: aleph nat le aleph omega
-- statement:
--   The Erdos1219 construction uses the aleph nat le aleph omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L83-L84
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L83-L84

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.aleph_nat_le_aleph_omega (N : ℕ) : ℵ_ (N : Ordinal.{u}) ≤ ℵ_ ω := by sorry
