-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_chi_flip_mem
-- name    : AaronsonAmbainis.Bridge.chi_flip_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:43.715169+00:00
-- url     : https://prove2.me/theorems/f5d3a13f-fbb4-403d-9035-5253a910a8cb
-- title:
--   Bridge: chi flip mem
-- statement:
--   Flipping a coordinate in `U` negates `χ_U`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L51-L58
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L51-L58

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.Bridge.chi_flip_mem {U : Finset ι} {j : ι} (hj : j ∈ U) (x : Cube ι) :
    chi U (flipSet x {j}) = -chi U x := by sorry
