-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_pm_sqrt_of_mainTheorem
-- name    : AaronsonAmbainis.Bridge.pm_sqrt_of_mainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:17:28.841917+00:00
-- url     : https://prove2.me/theorems/95abe412-6786-400d-abc0-a1f6a86cc7a7
-- title:
--   Bridge: pm sqrt of main Theorem
-- statement:
--   `Inf_i(p) ≥ (√15 / (500 π^4)) ε^{5/2} / d^6`, from `MainTheorem`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L299-L309
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedAA.lean#L299-L309

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.pm_sqrt_of_mainTheorem (h : MainTheorem) (n d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.totalDegree ≤ d) (hbd : ∀ X, |evPM p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPM p X - Ex (evPM p)) ^ 2) ≥ ε) :
    ∃ i, Ex (fun X => ((evPM p X - evPM p (flipBit X i)) / 2) ^ 2)
      ≥ Real.sqrt 15 / (500 * Real.pi ^ 4) * (ε ^ 2 * Real.sqrt ε) / (d : ℝ) ^ 6 := by sorry
