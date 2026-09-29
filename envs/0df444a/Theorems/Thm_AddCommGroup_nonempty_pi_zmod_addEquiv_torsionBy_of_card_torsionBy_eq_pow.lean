-- Prove2me | Theorems.Thm_AddCommGroup_nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow
-- name    : AddCommGroup.nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/11394e9c-b993-5f96-83e4-cdbddbd32cfb
-- title:
--   Recognising A[n] as (ℤ/n)^r from torsion counts
-- statement:
--   Let $A$ be an additive commutative group, let $n$ be a natural number with $n \neq 0$, and let $r$ be a natural number. Assume that for every natural number $d$ dividing $n$ the $d$-torsion subgroup of $A$, namely the $\mathbb{Z}$-submodule $\{a \in A : d \cdot a = 0\}$ (written `Submodule.torsionBy ℤ A d`, with $d$ regarded as an integer), has cardinality exactly $d^{r}$; here cardinality is `Nat.card`, so the hypothesis in particular forces each of these subgroups to be finite, since $d^{r} \neq 0$ for $d \mid n$ with $n \neq 0$. The conclusion is that the type of additive group isomorphisms from $\mathrm{Fin}\,r \to \mathbb{Z}/n\mathbb{Z}$ to the $n$-torsion subgroup of $A$ is nonempty, i.e. $A[n] \cong (\mathbb{Z}/n\mathbb{Z})^{r}$ as abelian groups. No finiteness, divisibility or flatness assumption on $A$ itself is imposed beyond the stated torsion counts.
--
--   This is the elementary recognition step which converts counts of torsion subgroups into an explicit structure statement: once $\#A[d] = d^{r}$ for all $d \mid n$, the group $A[n]$ is free of rank $r$ over $\mathbb{Z}/n\mathbb{Z}$. Its prime-power case is supplied by [`AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy`](thm.html#AddCommGroup.nonempty_basis_zmod_pow_of_card_torsionBy), which produces a $\mathbb{Z}/\ell^{m}$-basis indexed by `Fin r`; the result is used in the treatment of the $n$-torsion of abelian schemes over an algebraically closed base, where the counts $\#A[d] = d^{2g}$ are available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AddCommGroup.nonempty_pi_zmod_addEquiv_torsionBy_of_card_torsionBy_eq_pow
    {A : Type u} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0) (r : ℕ)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Fin r → ZMod n) ≃+ Submodule.torsionBy ℤ A n) := by sorry
