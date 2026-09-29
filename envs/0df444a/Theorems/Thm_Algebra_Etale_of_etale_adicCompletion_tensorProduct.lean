-- Prove2me | Theorems.Thm_Algebra_Etale_of_etale_adicCompletion_tensorProduct
-- name    : Algebra.Etale.of_etale_adicCompletion_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/d250a0fd-6f60-5a07-98ec-c47fdadf5333
-- title:
--   Étaleness descends from the maximal-adic completion
-- statement:
--   Let $R$ be a commutative Noetherian local ring, write $\mathfrak m =$ `IsLocalRing.maximalIdeal R` for its maximal ideal and $\widehat R =$ `AdicCompletion (IsLocalRing.maximalIdeal R) R` for the $\mathfrak m$-adic completion of $R$, and let $S$ be a commutative $R$-algebra. Assume that the base-changed algebra $\widehat R \otimes_R S$ is étale over $\widehat R$ in Mathlib's sense, namely formally étale and of finite presentation as a $\widehat R$-algebra. The conclusion is that $S$ is étale over $R$, again in the sense of `Algebra.Etale`: formally étale and of finite presentation over $R$. Thus étaleness of an $R$-algebra may be tested after completing the Noetherian local base. No hypothesis of finiteness, flatness or locality is imposed on $S$ beyond what is contained in the étaleness of the completed base change.
--
--   This is the descent direction of the standard principle that étaleness over a Noetherian local ring can be checked over the completion, obtained here as an instance of faithfully flat descent of étaleness. It is used in the proof of [`IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField`](thm.html#IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField), the criterion recognising étaleness of a finite algebra over a local ring from equality of ranks over the residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_of_etale_adicCompletion_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped TensorProduct in

theorem Algebra.Etale.of_etale_adicCompletion_tensorProduct
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (h : Algebra.Etale (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      ((AdicCompletion (IsLocalRing.maximalIdeal R) R) ⊗[R] S)) :
    Algebra.Etale R S := by sorry
