-- Prove2me | Theorems.Thm_BondySimonovits_ecount_union_right
-- name    : BondySimonovits.ecount_union_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:06:07.225795+00:00
-- url     : https://prove2.me/theorems/3780e744-39d9-4253-89da-e78df055ec77
-- title:
--   Bondy Simonovits: ecount union right
-- statement:
--   The Bondy Simonovits construction uses the ecount union right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L41-L46
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSGrowth.lean#L41-L46

module
public import Definitions.Def_BondySimonovitsLib_BSCycle
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj]

theorem BondySimonovits.ecount_union_right (A B B' : Finset V) (h : Disjoint B B') :
    ecount K A (B ∪ B') = ecount K A B + ecount K A B' := by sorry
