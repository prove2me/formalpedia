-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi_mul_chi_cube
-- name    : AaronsonAmbainis.Bridge.sum_chi_mul_chi_cube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:56:55.831363+00:00
-- url     : https://prove2.me/theorems/39a8630b-cb7d-4d7e-a5d9-19e7a2875982
-- title:
--   Bridge: sum chi mul chi cube
-- statement:
--   Orthogonality, summing over the cube.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L95-L97
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L95-L97

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.sum_chi_mul_chi_cube (S T : Finset ι) :
    ∑ x : Cube ι, chi S x * chi T x = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by sorry
