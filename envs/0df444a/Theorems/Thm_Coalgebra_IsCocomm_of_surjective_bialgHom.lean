-- Prove2me | Theorems.Thm_Coalgebra_IsCocomm_of_surjective_bialgHom
-- name    : Coalgebra.IsCocomm.of_surjective_bialgHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/704e940f-b1f2-5f60-ae34-05b6e2249057
-- title:
--   Cocommutativity descends along surjective bialgebra maps
-- statement:
--   Let $R$ be a commutative semiring, and let $A$ and $B$ be semirings carrying $R$-bialgebra structures, with $A$ assumed cocommutative in the sense of the Mathlib class `Coalgebra.IsCocomm R A`, i.e. the flip $\tau_A$ of $A \otimes_R A$ satisfies $\tau_A \circ \Delta_A = \Delta_A$. Let $\pi : A \to B$ be a bialgebra homomorphism over $R$ (an $R$-algebra map that is simultaneously a coalgebra map, so it commutes with the comultiplications and counits), and suppose that the underlying function of $\pi$ is surjective. The conclusion is that $B$ is cocommutative as well: the instance `Coalgebra.IsCocomm R B` holds, that is, the flip of $B \otimes_R B$ composed after $\Delta_B$ equals $\Delta_B$. No commutativity, flatness or finiteness hypotheses on $A$ or $B$ are imposed, and the base is only a commutative semiring.
--
--   This is the standard fact that a quotient of a cocommutative bialgebra, and more generally the image of a cocommutative bialgebra under a surjective bialgebra map, is again cocommutative; it is what lets quotient Hopf algebras (for instance those attached to quotients of commutative or cocommutative group schemes) inherit cocommutativity. It is used in the construction behind [`HopfAlgebra.exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp`](thm.html#HopfAlgebra.exists_formallyEtale_bialgHom_faithfullyFlat_ker_eq_map_ker_counit_zmodp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Coalgebra_IsCocomm_of_surjective_bialgHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem Coalgebra.IsCocomm.of_surjective_bialgHom
    {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A] [Coalgebra.IsCocomm R A]
    {B : Type*} [Semiring B] [Bialgebra R B] (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Coalgebra.IsCocomm R B := by sorry
