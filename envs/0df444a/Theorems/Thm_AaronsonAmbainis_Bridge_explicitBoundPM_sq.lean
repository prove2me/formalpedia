-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_explicitBoundPM_sq
-- name    : AaronsonAmbainis.Bridge.explicitBoundPM_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:24:46.51924+00:00
-- url     : https://prove2.me/theorems/c56e296b-c390-431c-9e61-2de740683e50
-- title:
--   Bridge: explicit Bound PM sq
-- statement:
--   Theorem 1.1 of the paper of this repository on `{-1,1}^n` (`true ↦ 1`, `false ↦ -1`), without
--   square roots: `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(p)²`, no hypothesis.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Capstone.lean#L59-L64
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Capstone.lean#L59-L64

import Definitions.Def_AaronsonAmbainis_Chain
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedAA
import Definitions.Def_AaronsonAmbainis_Conjecture
import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.explicitBoundPM_sq (n d : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ d)
    (hbd : ∀ X, |evPMt p X| ≤ 1) (ε : ℝ) (hε : 0 < ε)
    (hvar : Ex (fun X => (evPMt p X - Ex (evPMt p)) ^ 2) ≥ ε) :
    ∃ i, 3 * ε ^ 5 ≤ 50000 * Real.pi ^ 8 * (d : ℝ) ^ 12
      * Ex (fun X => ((evPMt p X - evPMt p (flipBit X i)) / 2) ^ 2) ^ 2 := by sorry
