-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_parity_not_hasDegreeLE
-- name    : AaronsonAmbainis.Bridge.parity_not_hasDegreeLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:21:31.865203+00:00
-- url     : https://prove2.me/theorems/1ab52e37-7bfa-4856-82f2-59839334d1b9
-- title:
--   Bridge: parity not has Degree LE
-- statement:
--   The full parity does not have degree `< n`: `HasDegreeLE` is not trivially true.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L190-L193
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Fourier.lean#L190-L193

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.parity_not_hasDegreeLE {d : ℕ} (hd : d < Fintype.card ι) :
    ¬ HasDegreeLE (chi (univ : Finset ι)) d := by sorry
