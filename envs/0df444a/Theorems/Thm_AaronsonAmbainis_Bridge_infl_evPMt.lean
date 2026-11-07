-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_infl_evPMt
-- name    : AaronsonAmbainis.Bridge.infl_evPMt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:14:38.637677+00:00
-- url     : https://prove2.me/theorems/74788ff7-cfaa-4fea-95aa-036e051e2060
-- title:
--   Bridge: infl ev PMt
-- statement:
--   The Bridge construction uses the infl ev PMt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L442-L446
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L442-L446

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.infl_evPMt {N : ℕ} (p : MvPolynomial (Fin N) ℝ) (i : Fin N) :
    Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      = Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2) := by sorry
