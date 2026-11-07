-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_sum_chi_mul_chi
-- name    : AaronsonAmbainis.Bridge.sum_chi_mul_chi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:58.75002+00:00
-- url     : https://prove2.me/theorems/d7766691-0c00-41c4-9c70-fba51c7c1d3f
-- title:
--   Bridge: sum chi mul chi
-- statement:
--   Orthogonality, summing over the characters.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L62-L77
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L62-L77

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.sum_chi_mul_chi (x y : Cube ι) :
    ∑ S : Finset ι, chi S x * chi S y = if x = y then (2 : ℝ) ^ Fintype.card ι else 0 := by sorry
