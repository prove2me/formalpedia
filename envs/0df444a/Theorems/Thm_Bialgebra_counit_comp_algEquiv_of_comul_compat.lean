-- Prove2me | Theorems.Thm_Bialgebra_counit_comp_algEquiv_of_comul_compat
-- name    : Bialgebra.counit_comp_algEquiv_of_comul_compat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/dea2a076-3972-53dc-8fff-917f40de6c94
-- title:
--   Comultiplication-compatible algebra isomorphisms preserve the counit
-- statement:
--   Let $K$ be a commutative ring and let $B_1$, $B_2$ be commutative rings carrying $K$-bialgebra structures, so each comes with a comultiplication $\Delta$ and counit $\varepsilon$ that are $K$-linear and satisfy the coassociativity and counit laws together with the compatibility with the ring structure. Let $\varphi \colon B_1 \to B_2$ be an isomorphism of $K$-algebras, and assume that $\varphi$ is compatible with comultiplication in the pointwise sense: for every $x \in B_1$ one has $\Delta_{B_2}(\varphi x) = (\varphi \otimes \varphi)(\Delta_{B_1} x)$, where $\varphi \otimes \varphi$ denotes the $K$-linear map $B_1 \otimes_K B_1 \to B_2 \otimes_K B_2$ induced by the underlying linear map of $\varphi$ in both factors. The conclusion is that $\varphi$ also respects the counits, again stated pointwise: for every $x \in B_1$, $\varepsilon_{B_2}(\varphi x) = \varepsilon_{B_1}(x)$ in $K$.
--
--   This is the uniqueness of the counit in the presence of a fixed comultiplication: a comultiplication-compatible algebra isomorphism of bialgebras automatically matches counits, so that coalgebra compatibility need only be checked for $\Delta$. It feeds the corresponding statement for antipodes of Hopf algebras and the descent of structure constants for Hopf orders with respect to a chosen basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_counit_comp_algEquiv_of_comul_compat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct in

theorem Bialgebra.counit_comp_algEquiv_of_comul_compat
    (K : Type*) [CommRing K]
    (B₁ : Type*) [CommRing B₁] [Bialgebra K B₁]
    (B₂ : Type*) [CommRing B₂] [Bialgebra K B₂]
    (φ : B₁ ≃ₐ[K] B₂)
    (hφcomul : ∀ x, Coalgebra.comul (R := K) (φ x) =
        (_root_.TensorProduct.map φ.toLinearMap φ.toLinearMap) (Coalgebra.comul (R := K) x)) :
    ∀ x, Coalgebra.counit (R := K) (φ x) = Coalgebra.counit (R := K) x := by sorry
