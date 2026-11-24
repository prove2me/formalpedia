-- Prove2me | Theorems.Thm_Erdos1219_Ctx_mem_prevU_B
-- name    : Erdos1219.Ctx.mem_prevU_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:44.352032+00:00
-- url     : https://prove2.me/theorems/ef64baea-17c1-4deb-83b9-732924a983ed
-- title:
--   Ctx: mem prev U B
-- statement:
--   The Ctx construction uses the mem prev U B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L347-L349
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L347-L349

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

theorem Erdos1219.Ctx.mem_prevU_B {i j : ℕ} (hij : i < j) {a : V} (ha : a ∈ S.Bu i) :
    a ∈ S.prevU j (fun i _ => S.B i) := by sorry
