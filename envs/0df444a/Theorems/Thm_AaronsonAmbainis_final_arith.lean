-- Prove2me | Theorems.Thm_AaronsonAmbainis_final_arith
-- name    : AaronsonAmbainis.final_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:59.007617+00:00
-- url     : https://prove2.me/theorems/27f7ef0c-7537-428a-b2c7-340f85b11f05
-- title:
--   Aaronson Ambainis: final arith
-- statement:
--   The final arithmetic: `VO * VN ≤ T * T * τ / 4` gives `4 * (VO / T) * (VN / T) ≤ τ`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/RemoveWeights.lean#L24-L28
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/RemoveWeights.lean#L24-L28

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_TwoSided_RemoveWeights
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.final_arith {VO VN T τ : ℝ} (hT : 0 < T) (h : VO * VN ≤ T * T * τ / 4) :
    4 * (VO / T) * (VN / T) ≤ τ := by sorry
