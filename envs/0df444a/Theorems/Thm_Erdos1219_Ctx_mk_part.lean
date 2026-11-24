-- Prove2me | Theorems.Thm_Erdos1219_Ctx_mk_part
-- name    : Erdos1219.Ctx.mk_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:43.466516+00:00
-- url     : https://prove2.me/theorems/8558d132-aa5f-46d2-8469-295371ad0152
-- title:
--   Ctx: mk part
-- statement:
--   The Ctx construction uses the mk part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L398-L401
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L398-L401

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

theorem Erdos1219.Ctx.mk_part (δ : Bool) (k : ℕ) : #(S.part δ k) = S.μ k := by sorry
