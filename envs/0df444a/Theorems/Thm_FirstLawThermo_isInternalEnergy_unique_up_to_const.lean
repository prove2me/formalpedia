-- Prove2me | Theorems.Thm_FirstLawThermo_isInternalEnergy_unique_up_to_const
-- name    : FirstLawThermo.isInternalEnergy_unique_up_to_const
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:49:55.048985+00:00
-- url     : https://prove2.me/theorems/8d54a7c4-61f9-466c-aec3-b2a525bfcda7
-- title:
--   Internal energy is unique up to an additive constant
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $O\in\sigma$ be a reference state such that every state $A$ is linked to $O$ by an adiabatic process in $\mathcal P$, going either from $O$ to $A$ or from $A$ to $O$. If $U$ and $U'$ are both internal energies for $\mathcal P$, then there is a constant $c\in\mathbb R$ with
--   $$U'(A)=U(A)+c\qquad\text{for every state }A.$$
--
--   Together with the previous milestone this says that internal energy is determined exactly up to an additive constant. It is "customarily stated relative to a conventionally chosen standard reference state of the system".
--
--   **Formalization Note** Only one direction of adiabatic accessibility is required for each state, in line with Münster's remark (quoted in the article) that it is not always possible to reach any state from any other by an adiabatic process.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Original statements: the thermodynamic approach": "It is defined only up to an arbitrary additive constant of integration ... The internal energy is customarily stated relative to a conventionally chosen standard reference state of the system."; Section "Evidence ...", subsection "Adiabatic processes" (adiabatic work from a reference state $O$ to an arbitrary state $A$, or from $A$ to $O$); Section "Various statements of the law for closed systems" (Münster 1970: not every state is adiabatically accessible from every other).

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.isInternalEnergy_unique_up_to_const {σ : Type*}
    (procs : Set (Process σ)) (O : σ) (hlink : AdiabaticallyLinkedTo procs O)
    (U U' : σ → ℝ) (hU : IsInternalEnergy procs U) (hU' : IsInternalEnergy procs U') :
    ∃ c : ℝ, ∀ A : σ, U' A = U A + c := by sorry
