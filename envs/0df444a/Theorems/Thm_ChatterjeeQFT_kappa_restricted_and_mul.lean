-- Prove2me | Theorems.Thm_ChatterjeeQFT_kappa_restricted_and_mul
-- name    : ChatterjeeQFT.kappa_restricted_and_mul
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:38:39.682567+00:00
-- url     : https://prove2.me/theorems/715db0cf-b065-4ce9-8e05-e42ba1084169
-- title:
--   $\kappa(A) \in SO^{\uparrow}(1,3)$ for $A \in SL(2,\mathbb{C})$, and $\kappa(AB) = \kappa(A)\kappa(B)$
-- statement:
--   For $A \in SL(2,\mathbb{C})$, the transformation $\kappa(A)$ of $\mathbb{R}^{1,3}$
--   defined by $M(\kappa(A)x) = A M(x) A^{\dagger}$ is linear and belongs to the restricted Lorentz
--   group: there is a matrix $L \in SO^{\uparrow}(1,3)$ with $\kappa(A)x = Lx$ for all $x$.
--   Furthermore $\kappa$ is multiplicative,
--
--   $$\kappa(AB) \;=\; \kappa(A)\circ\kappa(B),$$
--
--   so that $\kappa$ is a group homomorphism $SL(2,\mathbb{C}) \to SO^{\uparrow}(1,3)$. These are the
--   first two bullet points of §25.2; the determinant identity $\det M(x) = (x,x)$ gives the Lorentz
--   property, and continuity/connectedness of $SL(2,\mathbb{C})$ gives properness and
--   orthochronicity.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.2, p. 108 ("$\kappa(A)$ is a linear map on $\mathbb{R}^{1,3}$"; "$\kappa$ is a 2-to-1 surjective homomorphism from $SL(2,\mathbb{C})$ onto $SO^{\uparrow}(1,3)$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_SL2C
open Matrix
open scoped ComplexOrder

namespace ChatterjeeQFT

theorem kappa_restricted_and_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (∃ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L ∧ ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x)
      ∧ (∀ x : Fin 4 → ℝ, kappa (A * B) x = kappa A (kappa B x)) := by sorry

end ChatterjeeQFT
