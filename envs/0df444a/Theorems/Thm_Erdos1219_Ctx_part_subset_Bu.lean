-- Prove2me | Theorems.Thm_Erdos1219_Ctx_part_subset_Bu
-- name    : Erdos1219.Ctx.part_subset_Bu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:45.832883+00:00
-- url     : https://prove2.me/theorems/2a23f707-2a89-436e-9300-9d67e3601df1
-- title:
--   Ctx: part subset Bu
-- statement:
--   The Ctx construction uses the part subset Bu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L388-L391
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L388-L391

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

theorem Erdos1219.Ctx.part_subset_Bu (δ : Bool) (k : ℕ) : S.part δ k ⊆ S.Bu k := by sorry
