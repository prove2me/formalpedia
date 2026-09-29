-- Prove2me | Theorems.Thm_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy
-- name    : AddCommGroup.exists_basis_smul_eq_of_card_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/db5521cb-cfaf-5084-8e1a-bbfaffb0a167
-- title:
--   Lifting bases of M[ℓ^m] to bases of M[ℓ^{m+1}]
-- statement:
--   Let $\ell$ be a natural number assumed prime, let $M$ be an additive commutative group, and let $r, m$ be natural numbers. Assume the torsion counts $\#\,\{x \in M : \ell^j x = 0\} = (\ell^j)^r$ for every $j \le m+1$, the cardinality being taken of the $\mathbb{Z}$-submodule `Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)`. Let $V$ be an additive commutative group carrying a $\mathbb{Z}/\ell^m$-module structure, together with an injective additive map $\iota : V \to M$ whose range consists exactly of those $x \in M$ with $\ell^m x = 0$; and let $V'$ be an additive commutative group carrying a $\mathbb{Z}/\ell^{m+1}$-module structure, together with an injective additive map $\iota' : V' \to M$ whose range consists exactly of those $x \in M$ with $\ell^{m+1} x = 0$. Finally let $c$ be a basis of $V$ over $\mathbb{Z}/\ell^m$ indexed by `Fin r`. The conclusion is that there exists a basis $c'$ of $V'$ over $\mathbb{Z}/\ell^{m+1}$, again indexed by `Fin r`, such that $\iota(c_i) = \ell \cdot \iota'(c'_i)$ in $M$ for every $i$.
--
--   This is the inductive step in the standard argument that, for an abelian group whose $\ell$-power torsion has the exact counts $\#M[\ell^j] = \ell^{jr}$, each $M[\ell^n]$ is free of rank $r$ over $\mathbb{Z}/\ell^n$, with bases compatible under multiplication by $\ell$; it rests on the surjectivity of $\ell : M[\ell^{m+1}] \to M[\ell^m]$ recorded in [`AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy`](thm.html#AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy). It is used by [`AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy`](thm.html#AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy), which produces such a basis at each level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.exists_basis_smul_eq_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0)
    {V' : Type*} [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V']
    (ι' : V' →+ M) (hι' : Function.Injective ι')
    (hι'r : ∀ x : M, x ∈ ι'.range ↔ ((ℓ ^ (m + 1) : ℕ) : ℤ) • x = 0)
    (c : Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) :
    ∃ c' : Module.Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V', ∀ i, ι (c i) = ℓ • ι' (c' i) := by sorry
