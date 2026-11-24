-- Prove2me | Theorems.Thm_Erdos1219_Ctx_pick_mem
-- name    : Erdos1219.Ctx.pick_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:43.65717+00:00
-- url     : https://prove2.me/theorems/5cfbd2df-b244-4560-9057-bfc3b82c56c1
-- title:
--   Ctx: pick mem
-- statement:
--   The Ctx construction uses the pick mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L369-L370
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L369-L370

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

theorem Erdos1219.Ctx.pick_mem (i : ℕ) : S.pick i ∈ S.Bu i := by sorry
