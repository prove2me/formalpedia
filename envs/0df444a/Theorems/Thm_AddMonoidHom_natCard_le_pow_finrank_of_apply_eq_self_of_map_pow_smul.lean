-- Prove2me | Theorems.Thm_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
-- name    : AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/353b6bf0-b649-5c1b-85bc-9d61c70b8d32
-- title:
--   Cartier–Serre bound: C-fixed vectors in a K-subspace
-- statement:
--   Let $K \subseteq F$ be fields, $F$ a $K$-algebra, and let $M$ be an additive abelian group carrying compatible module structures over $F$ and over $K$ (a scalar tower $K \to F \to M$). Let $p$ be a prime, and assume $K$ is perfect of characteristic $p$. Let $C \colon M \to M$ be an additive endomorphism which is $p^{-1}$-semilinear over $F$, in the sense that $C(f^p \cdot m) = f \cdot C(m)$ for all $f \in F$ and $m \in M$, and let $W \subseteq M$ be a $K$-submodule that is finite-dimensional over $K$. Let $G$ be an abelian group and $\varphi \colon G \to M$ an injective additive map such that, for every $g \in G$, the element $\varphi(g)$ lies in $W$ and satisfies $C(\varphi(g)) = \varphi(g)$. The conclusion is the conjunction: $G$ is finite, and its cardinality satisfies $\#G \le p^{\,\dim_K W}$. Note that $C$ is only assumed semilinear for the $p$-th power map on $F$, no linearity over $K$ is assumed of $\varphi$, and $G$ carries no module structure.
--
--   This is the Cartier–Serre counting bound for the fixed points of an inverse-Frobenius-semilinear operator, in the form of a bound on the order of any abelian group that embeds additively into the $C$-fixed vectors of a finite-dimensional $K$-subspace. It is the basic finiteness input for the companion statements computing the order of a group of $C$-fixed points as exactly $p^{\dim_K}$ of a span, for counting fixed vectors of a Frobenius-semilinear map, and for bounding the rank of Hecke torsion on a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidHom_natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddMonoidHom.natCard_le_pow_finrank_of_apply_eq_self_of_map_pow_smul
    {K F M : Type*} [Field K] [Field F] [Algebra K F] [AddCommGroup M] [Module F M]
    [Module K M] [IsScalarTower K F M]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (C : M →+ M) (hsemi : ∀ (f : F) (m : M), C (f ^ p • m) = f • C m)
    (W : Submodule K M) [FiniteDimensional K W]
    {G : Type*} [AddCommGroup G] (φ : G →+ M) (hφ : Function.Injective φ)
    (hfix : ∀ g : G, C (φ g) = φ g) (hW : ∀ g : G, φ g ∈ W) :
    Finite G ∧ Nat.card G ≤ p ^ Module.finrank K W := by sorry
