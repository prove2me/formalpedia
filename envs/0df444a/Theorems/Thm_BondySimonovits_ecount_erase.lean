-- Prove2me | Theorems.Thm_BondySimonovits_ecount_erase
-- name    : BondySimonovits.ecount_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:03:00.61678+00:00
-- url     : https://prove2.me/theorems/246584e6-4230-4756-aeda-258a3d2b2d4c
-- title:
--   Bondy Simonovits: ecount erase
-- statement:
--   The Bondy Simonovits construction uses the ecount erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L81-L107
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSBasic.lean#L81-L107

module
public import Mathlib
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BondySimonovits
variable {V : Type*}

theorem BondySimonovits.ecount_erase [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] (X : Finset V) (u : V)
    (hu : u ∈ X) :
    ecount K X X = ecount K (X.erase u) (X.erase u) + 2 * (X.filter (K.Adj u)).card := by sorry
