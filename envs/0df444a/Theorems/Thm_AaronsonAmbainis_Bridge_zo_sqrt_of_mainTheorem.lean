-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_zo_sqrt_of_mainTheorem
-- name    : AaronsonAmbainis.Bridge.zo_sqrt_of_mainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:39.710199+00:00
-- url     : https://prove2.me/theorems/3fc555b8-447c-40fa-a497-b48f2c3e50b4
-- title:
--   Bridge: zo sqrt of main Theorem
-- statement:
--   `Inf_i[p] ≥ (8 √15 / (125 π^4)) ε^{5/2} / d^6`, from `MainTheorem`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L323-L332
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L323-L332

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.zo_sqrt_of_mainTheorem (h : MainTheorem) (N d : ℕ) (p : MvPolynomial (Fin N) ℝ)
    (hp : p.totalDegree ≤ d) (hrange : ∀ X, 0 ≤ ev01 p X ∧ ev01 p X ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (ev01 p X - Ex (ev01 p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => (ev01 p X - ev01 p (flipBit X i)) ^ 2)
      ≥ 8 * Real.sqrt 15 / (125 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by sorry
