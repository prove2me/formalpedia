-- Prove2me | Theorems.Thm_Erdos1219_Ctx_canonical
-- name    : Erdos1219.Ctx.canonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:48:47.539795+00:00
-- url     : https://prove2.me/theorems/44e65b58-8bdc-48aa-89e2-d6fb71079c65
-- title:
--   Ctx: canonical
-- statement:
--   The Ctx construction uses the canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L353-L363
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L353-L363

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

theorem Erdos1219.Ctx.canonical {i j : ℕ} (hij : i < j) {a a' b : V} (ha : a ∈ S.Bu i) (ha' : a' ∈ S.Bu i)
    (hb : b ∈ S.Bu j) : S.f a b = S.f a' b := by sorry
