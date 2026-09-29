-- Prove2me | Theorems.Thm_CartierDual_isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ
-- name    : CartierDual.isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/0d41282d-c575-5cd7-9794-96b0843a7b72
-- title:
--   Local–local is inherited by bialgebra quotients
-- statement:
--   Let $k$ be a field, and let $B$ and $B_1$ be commutative rings carrying $k$-bialgebra structures (in arbitrary universes), each finite as a $k$-module and each cocommutative as a $k$-coalgebra. Let $\pi \colon B \to B_1$ be a homomorphism of $k$-bialgebras which is surjective as a function, assume that $B$ is a local ring and that [`CartierDual k B`](def/HopfAlgebra_CartierDual.html#L12) — the $k$-linear dual $\operatorname{Hom}_k(B,k)$, equipped with the ring structure transported from the bialgebra structure of $B$ (convolution product, unit the counit) — is a local ring, and assume $B_1$ is nontrivial. Then $B_1$ is a local ring and [`CartierDual k B₁`](def/HopfAlgebra_CartierDual.html#L12), the $k$-linear dual of $B_1$ with its convolution ring structure, is a local ring as well. In the language of group schemes: a closed subgroup scheme $\operatorname{Spec} B_1 \subseteq \operatorname{Spec} B$ of a finite commutative group scheme which is local with local Cartier dual is again local with local Cartier dual.
--
--   This is the statement that the local–local property of a finite commutative group scheme over a field passes to closed subgroup schemes, in the form of bialgebra quotients; it is used in the analysis of Dieudonné modules, specifically in the comparison of the cardinality of the kernel of Frobenius with that of the cokernel of Verschiebung for a self-dual local–local group scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem CartierDual.isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ
    (k : Type u) [Field k] (B : Type v) (B₁ : Type w) [CommRing B] [Bialgebra k B] [CommRing B₁] [Bialgebra k B₁]
    [Module.Finite k B] [Module.Finite k B₁] [Coalgebra.IsCocomm k B] [Coalgebra.IsCocomm k B₁]
    (π : B →ₐc[k] B₁) (hπ : Function.Surjective π)
    (hloc : IsLocalRing B) (hdual : IsLocalRing (CartierDual k B)) [Nontrivial B₁] :
    IsLocalRing B₁ ∧ IsLocalRing (CartierDual k B₁) := by sorry
