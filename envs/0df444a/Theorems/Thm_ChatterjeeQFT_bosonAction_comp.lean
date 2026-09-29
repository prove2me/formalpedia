-- Prove2me | Theorems.Thm_ChatterjeeQFT_bosonAction_comp
-- name    : ChatterjeeQFT.bosonAction_comp
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:33:19.578411+00:00
-- url     : https://prove2.me/theorems/c5b79ce6-0a61-4c4f-8d2a-c25a4513cc63
-- title:
--   The Poincaré composition law $U(a,A)U(b,B) = U(a + Ab,\, AB)$ on scalar wave functions
-- statement:
--   The Poincaré group is $\mathcal{P} = \mathbb{R}^{1,3} \rtimes SO^{\uparrow}(1,3)$
--   with the group law $(a,A)(b,B) = (a + Ab,\, AB)$ (eq. (11.1)). The operators
--
--   $$(U(a,A)\psi)(p) = e^{i(a,p)}\, \psi(A^{-1}p)$$
--
--   of §11.3 form a representation of it: for all $a, b \in \mathbb{R}^{1,3}$ and all
--   $A, B \in SO^{\uparrow}(1,3)$,
--
--   $$U(a + Ab,\, AB) \;=\; U(a,A)\, U(b,B),$$
--
--   as an identity between operators on scalar wave functions on the mass shell. This is Postulate
--   P5's consistency requirement: changing the reference frame twice in succession is the same as
--   changing it once by the composite transformation.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 11 §11.1, eq. (11.1) p. 43 (the Poincaré group and its group law $(a,A)(b,B) = (a + Ab, AB)$) and §11.3, p. 45 (the representation for massive scalar bosons).

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
open MeasureTheory Matrix
open scoped ENNReal

namespace ChatterjeeQFT

theorem bosonAction_comp (a b : Fin 4 → ℝ) (A B : Matrix (Fin 4) (Fin 4) ℝ)
    (hA : IsRestrictedLorentz A) (hB : IsRestrictedLorentz B) (ψ : (Fin 4 → ℝ) → ℂ) :
    bosonAction (a + A *ᵥ b) (A * B) ψ = bosonAction a A (bosonAction b B ψ) := by sorry

end ChatterjeeQFT
