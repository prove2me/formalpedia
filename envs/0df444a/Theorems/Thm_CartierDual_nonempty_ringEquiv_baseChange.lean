-- Prove2me | Theorems.Thm_CartierDual_nonempty_ringEquiv_baseChange
-- name    : CartierDual.nonempty_ringEquiv_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/99c62cf0-d636-5811-9a55-66ceeae59e03
-- title:
--   Cartier duality commutes with base change
-- statement:
--   Let $R$ be a commutative ring, let $S$ be a commutative ring equipped with an $R$-algebra structure, and let $A$ be a commutative ring carrying a Hopf algebra structure over $R$ which is finite and free as an $R$-module and whose comultiplication is cocommutative. Here, for a bialgebra $B$ over a commutative ring $T$, [`CartierDual T B`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $T$-linear dual $\mathrm{Hom}_T(B,T)$ of $B$, endowed with the ring structure given by convolution (the product dual to the comultiplication of $B$); in the statement it is applied on the one hand to the base-changed bialgebra $S \otimes_R A$ over $S$, and on the other to $A$ over $R$. The assertion is that the type of ring isomorphisms
--   $$\mathrm{CartierDual}_S(S \otimes_R A) \;\simeq\; S \otimes_R \mathrm{CartierDual}_R(A)$$
--   is nonempty, i.e. that the Cartier dual of the base change of $A$ to $S$ is isomorphic as a ring to the base change to $S$ of the Cartier dual of $A$. The conclusion is stated as the nonemptiness of a type of ring isomorphisms rather than as a chosen isomorphism, so no compatibility of the isomorphism with the $S$-module structures or with the Hopf structures is recorded.
--
--   This is the standard compatibility of Cartier duality with base change for finite free commutative Hopf algebras. It is used in the analysis of finite flat group schemes attached to residual Galois representations, in particular to transfer information between a $\mathbb{Z}_p$-model and its special fibre, and is cited in the construction of unipotent models and in the study of inertia at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_nonempty_ringEquiv_baseChange.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.nonempty_ringEquiv_baseChange
    (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] :
    Nonempty (CartierDual S (S ⊗[R] A) ≃+* S ⊗[R] CartierDual R A) := by sorry
