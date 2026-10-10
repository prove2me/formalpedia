-- Prove2me | Theorems.Thm_FirstLawThermo_quasiStatic_adiabatic_work_eq_neg_deltaU
-- name    : FirstLawThermo.quasiStatic_adiabatic_work_eq_neg_deltaU
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:34.756738+00:00
-- url     : https://prove2.me/theorems/166a75f3-b4f6-4d5b-8f4a-abe01f927ed3
-- title:
--   Quasi-static adiabatic work through a reference state gives $-W_{A\to B}=U(B)-U(A)$
-- statement:
--   Let $\sigma$ be a set of states of a closed system and let $W_{A\to B}$ denote the quasi-static adiabatic work done by the system in going from state $A$ to state $B$. Fix a reference state $O$ and a function $U:\sigma\to\mathbb R$. Assume
--
--   1. formula (1): $W_{A\to O}=-W_{O\to A}$ for every state $A$;
--   2. the work from $A$ to $B$ may be computed along a path through $O$: $W_{A\to B}=W_{A\to O}+W_{O\to B}$ for all $A,B$;
--   3. $U(A)=U(O)-W_{O\to A}$ for every state $A$.
--
--   Then for all states $A,B$,
--   $$-W_{A\to B}=U(B)-U(A).$$
--
--   This is the article's chain of equalities showing that quasi-static adiabatic work between any two states is a difference of values of the internal energy.
--
--   **Formalization Note** The quasi-static adiabatic work is modelled as a real-valued function of the pair of states, so its independence of the path is built into the representation.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Evidence for the first law of thermodynamics for closed systems", subsection "Adiabatic processes": formula (1) $W^{\text{adiabatic, quasi-static}}_{A\to O}=-W^{\text{adiabatic, quasi-static}}_{O\to A}$, the definition $U(A)=U(O)-W^{\text{adiabatic}}_{O\to A}$, and the displayed chain $-W_{A\to B}=-W_{A\to O}-W_{O\to B}=W_{O\to A}-W_{O\to B}=-U(A)+U(B)=\Delta U$.

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem FirstLawThermo.quasiStatic_adiabatic_work_eq_neg_deltaU {σ : Type*}
    (W : σ → σ → ℝ) (U : σ → ℝ) (O : σ)
    (hrev : ∀ A : σ, W A O = -W O A)
    (hpath : ∀ A B : σ, W A B = W A O + W O B)
    (hU : ∀ A : σ, U A = U O - W O A) :
    ∀ A B : σ, -W A B = U B - U A := by sorry
