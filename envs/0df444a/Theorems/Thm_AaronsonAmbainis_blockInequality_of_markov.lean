-- Prove2me | Theorems.Thm_AaronsonAmbainis_blockInequality_of_markov
-- name    : AaronsonAmbainis.blockInequality_of_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:16.932481+00:00
-- url     : https://prove2.me/theorems/c811dbf6-e828-4fba-9e9d-6cd11bd4926b
-- title:
--   Aaronson Ambainis: block Inequality of markov
-- statement:
--   The block inequality, given Markov's inequality at an endpoint.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Block.lean#L20-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Block.lean#L20-L44

import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
import Definitions.Def_AaronsonAmbainis_Row_Gadget
import Definitions.Def_AaronsonAmbainis_Row_Block
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.blockInequality_of_markov : MarkovEndpoint → BlockInequality := by sorry
