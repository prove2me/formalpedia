-- Prove2me | Theorems.Thm_FirstLawThermo_first_law_internal_energy
-- name    : FirstLawThermo.first_law_internal_energy
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:54:59.923983+00:00
-- url     : https://prove2.me/theorems/01f0e9d3-2deb-48db-b906-52570c7f0128
-- title:
--   First law (mechanical approach): adiabatic work determines internal energy, unique up to a constant
-- statement:
--   Let $\mathcal P$ be a set of processes of a closed system with state set $\sigma$, and let $O\in\sigma$ be a reference state. Assume
--
--   1. $\mathcal P$ is closed under sequential composition of consecutive stages;
--   2. $\mathcal P$ contains the null process at every state;
--   3. adiabatic work is path independent in $\mathcal P$: adiabatic processes in $\mathcal P$ with the same initial and final states involve the same work done by the system;
--   4. every state $A$ is linked to $O$ by an adiabatic process in $\mathcal P$, from $O$ to $A$ or from $A$ to $O$.
--
--   Then
--
--   * there is an internal energy $U:\sigma\to\mathbb R$ for $\mathcal P$, that is
--   $$U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})=-W(p)\qquad\text{for every adiabatic }p\in\mathcal P;$$
--   * any two internal energies $U,U'$ for $\mathcal P$ differ by a constant: there is $c\in\mathbb R$ with $U'(A)=U(A)+c$ for every state $A$.
--
--   This is the first law of thermodynamics for closed systems in the mechanical approach (Bryan, Carathéodory, Born): the net work in adiabatic processes between two given states is the same regardless of the details of the process, and determines a state function, the internal energy, fixed up to an arbitrary additive constant.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Evidence for the first law of thermodynamics for closed systems", subsection "Adiabatic processes": "For all adiabatic processes between two specified states of a closed system of any nature, the net work done is the same regardless the details of the process, and determines a state function called internal energy, U."; Section "Conceptually revised statement, according to the mechanical approach"; Section "Various statements of the law for closed systems" (Carathéodory 1909: internal energy is a function of state, changed by the amount of work done adiabatically); Section "Original statements: the thermodynamic approach" (defined only up to an arbitrary additive constant).

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.first_law_internal_energy {σ : Type*} (procs : Set (Process σ)) (O : σ)
    (hcomp : ClosedUnderComp procs) (hnull : ContainsNull procs)
    (hpath : AdiabaticWorkPathIndependent procs) (hlink : AdiabaticallyLinkedTo procs O) :
    (∃ U : σ → ℝ, IsInternalEnergy procs U) ∧
      ∀ U U' : σ → ℝ, IsInternalEnergy procs U → IsInternalEnergy procs U' →
        ∃ c : ℝ, ∀ A : σ, U' A = U A + c := by sorry
