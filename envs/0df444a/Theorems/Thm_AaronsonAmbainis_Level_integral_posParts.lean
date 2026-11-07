-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_integral_posParts
-- name    : AaronsonAmbainis.Level.integral_posParts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:26.226892+00:00
-- url     : https://prove2.me/theorems/01380ead-bc1c-422c-876d-2e54707143e2
-- title:
--   Level: integral pos Parts
-- statement:
--   `∫_a^b (u - t)⁺ (t - v)⁺ dt = ((u - v)⁺)^3 / 6` when `a ≤ v` and `u ≤ b`
--   (Lemma 7.3 (i) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L39-L77
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integral.lean#L39-L77

import Mathlib
import Definitions.Def_AaronsonAmbainis_Level_Integral
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset

theorem AaronsonAmbainis.Level.integral_posParts {a b u v : ℝ} (hub : u ≤ b) (hav : a ≤ v) :
    ∫ t in a..b, max (u - t) 0 * max (t - v) 0 = max (u - v) 0 ^ 3 / 6 := by sorry
