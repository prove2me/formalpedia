-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_pmt_sqrt_of_mainTheorem
-- name    : AaronsonAmbainis.Bridge.pmt_sqrt_of_mainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:54.074719+00:00
-- url     : https://prove2.me/theorems/8dcb5dfd-cadc-423c-b7d3-ecba3e3e9efa
-- title:
--   Bridge: pmt sqrt of main Theorem
-- statement:
--   `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6` on `{-1,1}^n` with `true ↦ 1`, from
--   `MainTheorem`, with the power `5/2` written `ε² √ε`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L461-L469
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L461-L469

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.pmt_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by sorry
