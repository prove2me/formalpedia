-- Prove2me | Theorems.Thm_ChatterjeeQFT_kappa_surjective_two_to_one
-- name    : ChatterjeeQFT.kappa_surjective_two_to_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:40:01.754578+00:00
-- url     : https://prove2.me/theorems/00751584-502d-4da1-a8ca-5bb7de24d6b6
-- title:
--   $\kappa$ is a surjective $2$-to-$1$ homomorphism onto $SO^{\uparrow}(1,3)$
-- statement:
--   The map $\kappa$ is onto the restricted Lorentz group and exactly two-to-one:
--
--   - for every $L \in SO^{\uparrow}(1,3)$ there is $A \in SL(2,\mathbb{C})$ with $\kappa(A) = L$;
--   - for $A, B \in SL(2,\mathbb{C})$, $\kappa(A) = \kappa(B)$ if and only if $A = B$ or $A = -B$.
--
--   Thus $SL(2,\mathbb{C})$ is a double cover of $SO^{\uparrow}(1,3)$. This is what forces the
--   electron representation to be only *projective*: a section $\varrho$ of $\kappa$ can be chosen but
--   cannot be a homomorphism, and satisfies $\varrho(AB) = \pm\varrho(A)\varrho(B)$.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.2, p. 108 ("$\kappa$ is a 2-to-1 surjective homomorphism from $SL(2,\mathbb{C})$ onto $SO^{\uparrow}(1,3)$"; "$\kappa(A) = \kappa(B)$ if and only if either $A = B$ or $A = -B$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_SL2C
open Matrix
open scoped ComplexOrder

namespace ChatterjeeQFT

theorem kappa_surjective_two_to_one :
    (∀ L : Matrix (Fin 4) (Fin 4) ℝ, IsRestrictedLorentz L →
        ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ ∀ x : Fin 4 → ℝ, kappa A x = L *ᵥ x) ∧
      (∀ A B : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 → B.det = 1 →
        (kappa A = kappa B ↔ (A = B ∨ A = -B))) := by sorry

end ChatterjeeQFT
