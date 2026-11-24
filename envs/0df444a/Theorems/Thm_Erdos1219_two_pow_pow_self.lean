-- Prove2me | Theorems.Thm_Erdos1219_two_pow_pow_self
-- name    : Erdos1219.two_pow_pow_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:40:24.254414+00:00
-- url     : https://prove2.me/theorems/84b8e567-b926-47b7-bdad-7574db144dbd
-- title:
--   Erdos1219: two pow pow self
-- statement:
--   The Erdos1219 construction uses the two pow pow self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L34-L36
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L34-L36

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.two_pow_pow_self {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    ((2 : Cardinal.{u}) ^ μ) ^ μ = 2 ^ μ := by sorry
