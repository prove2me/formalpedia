-- Prove2me | Theorems.Thm_Erdos1219_Ctx_cross
-- name    : Erdos1219.Ctx.cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:42.91178+00:00
-- url     : https://prove2.me/theorems/2abcf129-a5df-4546-b5ec-e664f9fffc63
-- title:
--   Ctx: cross
-- statement:
--   The Ctx construction uses the cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L375-L381
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L375-L381

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)

theorem Erdos1219.Ctx.cross {i j : ℕ} (hij : i < j) {a b : V} (ha : a ∈ S.Bu i) (hb : b ∈ S.Bu j) :
    S.f a b = S.g i j := by sorry
