-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_fourier_unique
-- name    : AaronsonAmbainis.Bridge.fourier_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:49.274942+00:00
-- url     : https://prove2.me/theorems/6b57b1ef-7962-4cdb-9710-b21fa4d9f364
-- title:
--   Bridge: fourier unique
-- statement:
--   The coefficients of a character expansion are unique: they are the Fourier coefficients.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L134-L157
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L134-L157

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.fourier_unique {f : Cube ι → ℝ} {c : Finset ι → ℝ}
    (hf : ∀ x, f x = ∑ S, c S * chi S x) (T : Finset ι) : c T = fourier f T := by sorry
