-- Prove2me | Theorems.Thm_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy
-- name    : AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/25a40303-78c9-5fd5-b2b0-184cde22f98a
-- title:
--   Levelwise torsion counts give a free ℤ/ℓ^m-module of rank r
-- statement:
--   Let $\ell$ be a natural number which is prime, let $M$ be an additive commutative group, and let $r,m$ be natural numbers. Assume the counting hypothesis: for every $j \le m$ the submodule $\{x \in M : \ell^{j} x = 0\}$ of $M$, viewed as the $\mathbb Z$-torsion submodule of $M$ by the integer $\ell^{j}$, has cardinality $(\ell^{j})^{r}$ (as a natural-number cardinality, so finiteness is part of the assertion). Let $V$ be an additive commutative group equipped with a module structure over $\mathbb Z/\ell^{m}$, and let $\iota \colon V \to M$ be an additive group homomorphism which is injective and whose image is exactly the $\ell^{m}$-torsion of $M$, in the sense that for every $x \in M$ one has $x \in \operatorname{range}\iota$ if and only if $\ell^{m} x = 0$. The conclusion is that the type of bases of $V$ as a $\mathbb Z/\ell^{m}$-module indexed by $\mathrm{Fin}\, r$ is nonempty; that is, $V$ is free of rank $r$ over $\mathbb Z/\ell^{m}$, hence $V \cong (\mathbb Z/\ell^{m})^{r}$.
--
--   This is the standard structure statement for $\ell$-power torsion: an abelian group whose $\ell^{j}$-torsion has order $\ell^{jr}$ for all $j \le m$ has $\ell^{m}$-torsion free of rank $r$ over $\mathbb Z/\ell^{m}$, the counts at all lower levels being genuinely needed. Phrasing the torsion subgroup through an injection $\iota$ with the indicated image allows the result to be applied to any concrete model of the $\ell^{m}$-torsion carrying its own $\mathbb Z/\ell^{m}$-module structure; it is used in the construction of $\mathbb Z/\ell^{m}$-bases of torsion of divisor class groups and in passing to $\ell$-adic limits.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_nonempty_basis_zmod_pow_of_card_torsionBy.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0) :
    Nonempty (Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) := by sorry
