-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_fourier
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_iff_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:59:32.443384+00:00
-- url     : https://prove2.me/theorems/9bd0deb9-e307-45d0-8d98-07495bf8b1cc
-- title:
--   Bridge: has Degree LE iff fourier
-- statement:
--   `HasDegreeLE f d` says exactly that the Fourier coefficients above level `d` vanish.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L160-L167
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L160-L167

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_iff_fourier {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ ∀ S : Finset ι, d < S.card → fourier f S = 0 := by sorry
