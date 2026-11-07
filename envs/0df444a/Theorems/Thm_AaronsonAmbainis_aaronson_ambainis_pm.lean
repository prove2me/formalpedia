-- Prove2me | Theorems.Thm_AaronsonAmbainis_aaronson_ambainis_pm
-- name    : AaronsonAmbainis.aaronson_ambainis_pm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:26:00.452401+00:00
-- url     : https://prove2.me/theorems/f2df426e-dfd0-4e2e-98ae-71048b9f7390
-- title:
--   Aaronson Ambainis: aaronson ambainis pm
-- statement:
--   Theorem 1.1 of the paper of this repository (`paper/aaronson_ambainis_paper.pdf`), on the cube
--   `{-1,1}^n`, with the explicit lower bound `(√15 / (500 π^4)) ε^{5/2} / d^6`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Main.lean#L43-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Main.lean#L43-L44

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Main
set_option autoImplicit true
open AaronsonAmbainis

theorem AaronsonAmbainis.aaronson_ambainis_pm : ExplicitBoundPM := by sorry
