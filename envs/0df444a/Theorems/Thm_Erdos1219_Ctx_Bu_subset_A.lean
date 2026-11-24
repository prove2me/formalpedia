-- Prove2me | Theorems.Thm_Erdos1219_Ctx_Bu_subset_A
-- name    : Erdos1219.Ctx.Bu_subset_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:46.198716+00:00
-- url     : https://prove2.me/theorems/dddc0e9f-41c9-44ab-af72-18f9f00cfb6d
-- title:
--   Ctx: Bu subset A
-- statement:
--   The Ctx construction uses the Bu subset A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L345-L345
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L345-L345

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

theorem Erdos1219.Ctx.Bu_subset_A (k : ℕ) : S.Bu k ⊆ S.A k := by sorry
