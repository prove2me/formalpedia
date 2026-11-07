-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_chi_mul_chi
-- name    : AaronsonAmbainis.Bridge.chi_mul_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:37.351484+00:00
-- url     : https://prove2.me/theorems/b5e7d736-dba9-4332-99df-080d5230400e
-- title:
--   Bridge: chi mul chi
-- statement:
--   `χ_S χ_T = χ_{S Δ T}`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L41-L47
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L41-L47

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.chi_mul_chi (S T : Finset ι) (x : Cube ι) :
    chi S x * chi T x = chi (symmDiff S T) x := by sorry
