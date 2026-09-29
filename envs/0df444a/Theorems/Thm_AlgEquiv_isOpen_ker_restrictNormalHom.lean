-- Prove2me | Theorems.Thm_AlgEquiv_isOpen_ker_restrictNormalHom
-- name    : AlgEquiv.isOpen_ker_restrictNormalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/02a6bcea-f03b-5072-bcaf-377c1a8bc452
-- title:
--   Kernel of restriction to a finite normal subextension is open
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, and let $E$ be a further field that is both a $K$-algebra and a subalgebra-like intermediate layer, in the sense that $L$ is an $E$-algebra and the scalar actions form a tower $K \to E \to L$. Assume $E$ is normal over $K$ and finite-dimensional over $K$. Then the kernel of the restriction homomorphism $\mathrm{restrictNormalHom}\,E \colon (L \simeq_{\mathrm{alg}[K]} L) \to (E \simeq_{\mathrm{alg}[K]} E)$, which sends a $K$-algebra automorphism of $L$ to the automorphism of $E$ it induces through the tower map (normality of $E/K$ guaranteeing that the induced map lands in $E$), is an open subset of the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$, taken with its Krull topology. No separability, algebraicity or normality hypothesis on $L/K$ is imposed; the conclusion is openness of the kernel as a set, the group structure being recorded only through the monoid homomorphism whose kernel it is.
--
--   This is the standard fact that a $K$-automorphism group of $L$ acts with open kernel on a finite normal subextension, so that restriction to $E$ is continuous for the discrete topology on $\mathrm{Aut}_K(E)$; in the classical setting $K = \mathbb{Q}$, $L = \overline{\mathbb{Q}}$ and $E$ a number field Galois over $\mathbb{Q}$, it supplies the openness of the kernel of a Galois representation that is trivial on $\mathrm{Gal}(\overline{\mathbb{Q}}/E)$. It is used in the construction of the matrix realisations of eigenform-attached representations, via [`FreyPackage.eigenformRealizationSupplyFieldAtFamily`](thm.html#FreyPackage.eigenformRealizationSupplyFieldAtFamily).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgEquiv_isOpen_ker_restrictNormalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgEquiv.isOpen_ker_restrictNormalHom (K L : Type*) [Field K] [Field L] [Algebra K L]
    (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L] [Normal K E]
    [FiniteDimensional K E] :
    IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker : Set (L ≃ₐ[K] L)) := by sorry
