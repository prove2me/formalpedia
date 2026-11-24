-- Prove2me | Theorems.Thm_Erdos1219_le_two_pow_self
-- name    : Erdos1219.le_two_pow_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:15.107288+00:00
-- url     : https://prove2.me/theorems/d71fb0b7-87f3-4e9d-ba7d-1a9662cd9f27
-- title:
--   Erdos1219: le two pow self
-- statement:
--   The Erdos1219 construction uses the le two pow self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L38-L38
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L38-L38

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.le_two_pow_self {μ : Cardinal.{u}} : μ ≤ 2 ^ μ := by sorry
