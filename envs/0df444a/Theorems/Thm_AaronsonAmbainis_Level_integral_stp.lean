-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_integral_stp
-- name    : AaronsonAmbainis.Level.integral_stp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:19.738729+00:00
-- url     : https://prove2.me/theorems/e4811a0b-736b-4326-a91b-063adefd8721
-- title:
--   Level: integral stp
-- statement:
--   `∫_a^b 1_{c ≤ t} dt = b - c` for `c` in `[a, b]` (this gives Lemma 7.3 (ii) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L95-L111
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L95-L111

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.integral_stp {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) : ∫ t in a..b, stp c t = b - c := by sorry
