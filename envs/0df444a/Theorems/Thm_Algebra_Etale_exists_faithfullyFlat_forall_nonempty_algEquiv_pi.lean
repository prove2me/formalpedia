-- Prove2me | Theorems.Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi
-- name    : Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/8fd999a6-715a-5576-bbb1-e9ec628190b2
-- title:
--   Simultaneous splitting of finitely many finite étale algebras
-- statement:
--   Let $R$ be a commutative ring, let $\iota$ be a finite index type, and let $(B_i)_{i \in \iota}$ be a family of commutative rings, each equipped with an $R$-algebra structure, each finite as an $R$-module and each étale over $R$ (`Algebra.Etale R (B i)`). Let $\deg : \iota \to \mathbb{N}$ and assume that for every $i$ the stalkwise rank function of $B_i$ is the constant function $\deg i$, i.e. `Module.rankAtStalk (R := R) (B i)` equals $\deg i$ as a function on $\operatorname{Spec} R$. The conclusion asserts the existence of a type $R'$ in the same universe as $R$ and the $B_i$, together with a commutative ring structure on $R'$ and an $R$-algebra structure, such that $R'$ is finite as an $R$-module, étale over $R$ and faithfully flat over $R$, and such that for every $i$ the type of $R'$-algebra isomorphisms $R' \otimes_R B_i \simeq (\mathrm{Fin}(\deg i) \to R')$ is nonempty; that is, one single finite étale faithfully flat base change simultaneously trivialises all the $B_i$, turning each into a product of $\deg i$ copies of $R'$.
--
--   This is the standard statement that finitely many finite étale covers of constant degree are simultaneously split by a single finite étale surjective base change. It is used in the construction of Deligne–Rapoport style model packages for modular curves, where locally split pools of étale algebras over a base are required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Etale_exists_faithfullyFlat_forall_nonempty_algEquiv_pi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.Etale.exists_faithfullyFlat_forall_nonempty_algEquiv_pi
    (R : Type u) [CommRing R]
    {ι : Type} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    [∀ i, Module.Finite R (B i)] [∀ i, Algebra.Etale R (B i)]
    (deg : ι → ℕ) (hdeg : ∀ i, Module.rankAtStalk (R := R) (B i) = deg i) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.Finite R R' ∧ Algebra.Etale R R' ∧ Module.FaithfullyFlat R R' ∧
      ∀ i, Nonempty (R' ⊗[R] (B i) ≃ₐ[R'] (Fin (deg i) → R')) := by sorry
