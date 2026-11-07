-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_fourier_inversion
-- name    : AaronsonAmbainis.Bridge.fourier_inversion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:11.587872+00:00
-- url     : https://prove2.me/theorems/ab13439e-7e7d-47f6-97d3-fffac5bfad1f
-- title:
--   Bridge: fourier inversion
-- statement:
--   Fourier inversion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L104-L126
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L104-L126

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.fourier_inversion (f : Cube ι → ℝ) (x : Cube ι) :
    ∑ S, fourier f S * chi S x = f x := by sorry
