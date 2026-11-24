-- Prove2me | Theorems.Thm_Erdos1219_aleph_omega_le_of_forall_nat
-- name    : Erdos1219.aleph_omega_le_of_forall_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:43.281014+00:00
-- url     : https://prove2.me/theorems/00b6144a-30ae-48b0-b34f-79fc50ebd30b
-- title:
--   Erdos1219: aleph omega le of forall nat
-- statement:
--   The Erdos1219 construction uses the aleph omega le of forall nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L86-L93
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L86-L93

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.aleph_omega_le_of_forall_nat {c : Cardinal.{u}}
    (h : ∀ N : ℕ, ℵ_ (N : Ordinal.{u}) ≤ c) : ℵ_ ω ≤ c := by sorry
