-- Prove2me | Theorems.Thm_FirstLawThermo_exists_isInternalEnergy
-- name    : FirstLawThermo.exists_isInternalEnergy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:50:23.446353+00:00
-- url     : https://prove2.me/theorems/b69a0f8d-d1a0-465d-9ed4-302065690b72
-- title:
--   Path-independent adiabatic work defines an internal energy
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $O\in\sigma$ be a reference state. Assume
--
--   1. $\mathcal P$ is closed under sequential composition of consecutive stages;
--   2. $\mathcal P$ contains the null process at every state;
--   3. adiabatic work is path independent in $\mathcal P$: adiabatic processes in $\mathcal P$ with the same initial and final states involve the same work;
--   4. every state $A$ is linked to $O$ by an adiabatic process in $\mathcal P$, from $O$ to $A$ or from $A$ to $O$.
--
--   Then there is a function $U:\sigma\to\mathbb R$ with $U(O)=0$ such that
--   $$U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})=-W(p)\qquad\text{for every adiabatic }p\in\mathcal P.$$
--
--   This is the existence half of the statement that the net adiabatic work "determines a state function called internal energy, $U$". The normalization $U(O)=0$ fixes the arbitrary reference level at the reference state.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Evidence for the first law of thermodynamics for closed systems", subsection "Adiabatic processes": "For all adiabatic processes between two specified states of a closed system of any nature, the net work done is the same regardless the details of the process, and determines a state function called internal energy, U."; also "In an adiabatic process, adiabatic work takes the system either from a reference state $O$ with internal energy $U(O)$ to an arbitrary one $A$ with internal energy $U(A)$, or from the state $A$ to the state $O$: $U(A)=U(O)-W^{\text{adiabatic}}_{O\to A}$ or $U(O)=U(A)-W^{\text{adiabatic}}_{A\to O}$", and the discussion of "the time order of the stages, and their relative magnitudes".

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.exists_isInternalEnergy {σ : Type*} (procs : Set (Process σ)) (O : σ)
    (hcomp : ClosedUnderComp procs) (hnull : ContainsNull procs)
    (hpath : AdiabaticWorkPathIndependent procs) (hlink : AdiabaticallyLinkedTo procs O) :
    ∃ U : σ → ℝ, IsInternalEnergy procs U ∧ U O = 0 := by sorry
