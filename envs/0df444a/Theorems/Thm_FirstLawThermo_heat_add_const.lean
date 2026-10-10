-- Prove2me | Theorems.Thm_FirstLawThermo_heat_add_const
-- name    : FirstLawThermo.heat_add_const
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:53:04.143997+00:00
-- url     : https://prove2.me/theorems/0fb6a2cb-85d6-4a8b-bb99-e2053083aa3c
-- title:
--   Heat does not depend on the reference level of internal energy
-- statement:
--   Let $\sigma$ be the state set of a closed system, $U:\sigma\to\mathbb R$ a function, $c\in\mathbb R$ a constant and $p$ any process. Then
--   $$Q_{U+c}(p)=Q_U(p),$$
--   where $U+c$ denotes the function $A\mapsto U(A)+c$.
--
--   Since the internal energy is only defined up to an additive constant, this shows that the heat, defined as a residual, is nevertheless a well-defined quantity attached to the process.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Original statements: the thermodynamic approach" (internal energy defined only up to an additive constant); Section "Various statements of the law for closed systems" (heat defined as a residual difference between change of internal energy and work); Section "Definition": "Heat and work are said to be path dependent, while change in internal energy depends only on the initial and final states".

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.heat_add_const {σ : Type*} (U : σ → ℝ) (c : ℝ) (p : Process σ) :
    heat (fun A => U A + c) p = heat U p := by sorry
