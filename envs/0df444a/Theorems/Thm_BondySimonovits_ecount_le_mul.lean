-- Prove2me | Theorems.Thm_BondySimonovits_ecount_le_mul
-- name    : BondySimonovits.ecount_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:54.715317+00:00
-- url     : https://prove2.me/theorems/cbf59091-64e2-4652-b7ed-5501e87ab16c
-- title:
--   Bondy Simonovits: ecount le mul
-- statement:
--   The Bondy Simonovits construction uses the ecount le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L49-L53
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L49-L53

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]
omit [DecidableEq V]

theorem BondySimonovits.ecount_le_mul (A B : Finset V) : ecount K A B ≤ A.card * B.card := by sorry
