-- Prove2me | Theorems.Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
-- name    : AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/5ede15a5-3d29-577e-ad43-058697fc4a59
-- title:
--   σ-stable cyclic subgroups of order n number ν₂(n)
-- statement:
--   Let $A$ be an additive abelian group and let $n$ be a nonzero natural number. Suppose given an isomorphism of additive groups $e$ between $\mathbb{Z}/n \times \mathbb{Z}/n$ and the $n$-torsion submodule `Submodule.torsionBy ℤ A n` of $A$ viewed as a $\mathbb{Z}$-module, i.e. $A[n] \cong (\mathbb{Z}/n)^2$. Let $\sigma : A \to A$ be an additive endomorphism satisfying $\sigma(\sigma a) = -a$ for every $a \in A$, and assume that $\sigma$ is non-scalar at every prime dividing $n$ in the following sense: for each prime $p \mid n$ there exists $a \in A$ of additive order exactly $p$ such that $\sigma a \neq k \cdot a$ for every natural number $k$. Then the number of subgroups $H \leq A$ that are additively cyclic, have cardinality $n$, and satisfy $\sigma(H) = H$ (as the image `H.map σ`) is finite and equal to $\nu_2(n)$, which by definition is the number of $x \in \mathbb{Z}/n$ with $x^2 + 1 = 0$.
--
--   This is the group-theoretic core of the count of elliptic points of order $2$ on the modular curve $Y_0(N)$: for an endomorphism with $\sigma^2 = -1$ acting non-scalarly on $p$-torsion for each $p \mid N$, the $\sigma$-stable cyclic subgroups of order $N$ correspond to the square roots of $-1$ in $\mathbb{Z}/N$. It is applied at the level of Weierstrass curves in the statements counting cyclic subgroups of order $N$ fixed by the automorphism $[i]$ of $y^2 = x^3 + Ax$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddCommGroup_natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo.lean

import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem AddCommGroup.natCard_isAddCyclic_addSubgroup_map_eq_of_sq_eq_neg_one_eq_nuTwo
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (σ : A →+ A) (hσ : ∀ a : A, σ (σ a) = -a)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    Nat.card {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = n ∧ H.map σ = H}
      = nuTwo n := by sorry
