-- Prove2me | Theorems.Thm_FirstLawThermo_isInternalEnergy_add_const
-- name    : FirstLawThermo.isInternalEnergy_add_const
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:49:24.886154+00:00
-- url     : https://prove2.me/theorems/41a75d07-6c44-4b1b-bdca-e9758a7795b5
-- title:
--   Internal energy may be shifted by an arbitrary constant
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $U:\sigma\to\mathbb R$ be an internal energy for $\mathcal P$, i.e. $U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})=-W(p)$ for every adiabatic $p\in\mathcal P$. Then for every constant $c\in\mathbb R$ the function
--   $$A\longmapsto U(A)+c$$
--   is again an internal energy for $\mathcal P$.
--
--   This is half of the statement that the internal energy is defined only up to an arbitrary additive constant, which can be adjusted to give an arbitrary reference zero level.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Original statements: the thermodynamic approach": "Because of its definition in terms of increments, the value of the internal energy of a system is not uniquely defined. It is defined only up to an arbitrary additive constant of integration, which can be adjusted to give arbitrary reference zero levels."

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.isInternalEnergy_add_const {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (c : ℝ) :
    IsInternalEnergy procs (fun A => U A + c) := by sorry
